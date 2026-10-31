{- | The codebase on disk (design §7.4).

A store is a directory:

@
format          "eval codebase 11"
terms\/\<hex\>    one term per file, in the storage encoding ("Eval.Hash")
types\/\<hex\>    one declared type per file (design §6.1)
names.log       append-only: time, then  bind name ref | unname name | unit name | chart name | prefer text | unprefer text | type name hex | con name hex.i | field name hex.i.j | use path [as alias] | unuse path [as alias] | sig name type | unsig name
@

Terms are content-addressed, so they never conflict and are only ever
added. Everything label-level (names, their history, unit declarations,
the stored default @use@s) is the log replayed in order, which is also
what makes two stores mergeable: concatenate the logs and sort by time,
which is what 'mergeStore' does.

The standard library lives in the store like everything else (design
§7.7). A new store is seeded with it: its terms and types are written,
and its labels and its stored @use@s are written to the log stamped with time
0, so they sort before every line of the user's and are the same lines in
every store, which a merge then recognises. A store is loaded on top of
the empty codebase; nothing is entered in memory first. A store opens only
at the current format; a store of another format is refused (design §7.4).
-}
module Eval.Store (
  Store (..),
  Seed (..),
  stdlibSeed,
  formatVersion,
  locateStore,
  openStore,
  seedStore,
  loadStore,
  sync,
  MergeReport (..),
  mergeStore,
  mergeStores,
) where

import Control.Monad (foldM, foldM_, forM_, unless, void, when)
import Data.ByteString qualified as BS
import Data.Either (lefts, rights)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Text.Read qualified as TR
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Codebase
import Eval.Core
import Eval.Dimension (Spelling (..))
import Eval.Hash
import Eval.Parser (parseType)
import Eval.Prelude (stdlibCodebase)
import Eval.Resolve (renderResolveError, signatureScheme, storeTerm)
import Eval.Syntax (Use (..), renderUse, rootScope)
import Eval.TCore (signatureHolds)
import Eval.Type (Scheme, TypeDef (..), renderSignature)
import System.Directory
import System.FilePath

newtype Store = Store {dir :: FilePath}

formatLine :: Int -> Text
formatLine v = "eval codebase " <> tshow v

{- | Bumped whenever the store's layout changes: the storage encoding
('storageVersion'), the log's lines, or what a store holds, the library
included. A store opens only at this format; a store of another format is
refused with one line (design §7.4).
-}
formatVersion :: Int
formatVersion = 11

{- | The store to use: the directory given, else a @.eval@ directory found by
walking up from the working directory, else the user store under
@$XDG_DATA_HOME\/eval@.
-}
locateStore :: Maybe FilePath -> IO FilePath
locateStore = \case
  Just d -> pure d
  Nothing -> do
    cwd <- getCurrentDirectory
    local <- findUp cwd
    maybe (getXdgDirectory XdgData "eval") pure local
 where
  findUp d = do
    let candidate = d </> ".eval"
    present <- doesDirectoryExist candidate
    if present
      then pure (Just candidate)
      else
        let parent = takeDirectory d
         in if parent == d then pure Nothing else findUp parent

{- | What a new store is seeded with (design §7.7): the library's codebase,
with its stored @use@s.
-}
newtype Seed = Seed {library :: Codebase}

-- | The standard library as a 'Seed'.
stdlibSeed :: Either Text Seed
stdlibSeed = Seed <$> stdlibCodebase

{- | Create the directory if needed and seed it, or check that an existing
one is ours. The seed is only looked at to create a store, so opening an
existing one never enters the library in memory: the store has it. A store
of another format is refused and left as it is (design §7.4), and so is
one whose format file says anything else.
-}
openStore :: Either Text Seed -> FilePath -> IO (Either Text Store)
openStore seeding d = do
  let formatFile = d </> "format"
  present <- doesFileExist formatFile
  if not present
    then case seeding of
      Left err -> pure (Left ("the standard library does not load:\n" <> err))
      Right seed -> do
        directories
        -- The format file last, so an interrupted seeding is seeded again.
        seedStore (Store d) seed.library
        TIO.writeFile formatFile (formatLine formatVersion <> "\n")
        pure (Right (Store d))
    else do
      line <- T.strip <$> TIO.readFile formatFile
      if line == formatLine formatVersion
        then directories >> pure (Right (Store d))
        else pure . Left $ case TR.decimal <$> T.stripPrefix "eval codebase " line of
          Just (Right (v, "")) ->
            T.pack d
              <> ": this codebase is format "
              <> tshow (v :: Integer)
              <> "; this eval opens format "
              <> tshow formatVersion
          _ ->
            T.pack d <> " is not an eval codebase (its format file says \"" <> line <> "\")"
 where
  directories = do
    createDirectoryIfMissing True (d </> "terms")
    createDirectoryIfMissing True (d </> "types")

{- | The time a seeded store's library lines carry (design §7.7): 0, before
any line of the user's, and the same in every store, so a merge of two
seeded stores adds nothing for the library.
-}
seedStamp :: Text
seedStamp = "0"

{- | Seed a store with a codebase, the library (design §7.7): its type and
term files, then its labels and stored @use@s as log lines at time 0,
before whatever the log already holds. The log is written whole, through a
temporary file, after the terms.
-}
seedStore :: Store -> Codebase -> IO ()
seedStore store seed = do
  writeContent store emptyCodebase seed
  let logFile = store.dir </> "names.log"
  present <- doesFileExist logFile
  old <- if present then TIO.readFile logFile else pure ""
  let tmp = store.dir </> "names.log.seed"
  TIO.writeFile tmp (T.unlines (logEntries seedStamp emptyCodebase seed) <> old)
  renameFile tmp logFile

{- | Load the store on top of a codebase, the empty one at start: decode
every term, check and add them dependencies first, then replay the log.
Problems are reported as notes and the rest still loads.
-}
loadStore :: Store -> Codebase -> IO (Codebase, [Text])
loadStore store base = do
  typesPresent <- doesDirectoryExist (store.dir </> "types")
  typeFiles <-
    if typesPresent then listDirectory (store.dir </> "types") else pure []
  decodedTypes <- mapM readType typeFiles
  -- Types first: terms mention them, they mention only each other.
  let withTypes =
        foldl (\acc (h, def) -> addTypeDef h def acc) base (rights decodedTypes)
  files <- listDirectory (store.dir </> "terms")
  decoded <- mapM readTerm files
  let loaded = Map.fromList [(h, t) | Right (h, t) <- decoded]
      decodeNotes = lefts decodedTypes ++ lefts decoded
  let (cb, enterNotes) = enterAll loaded withTypes
  let logFile = store.dir </> "names.log"
  present <- doesFileExist logFile
  logLines <- if present then T.lines <$> TIO.readFile logFile else pure []
  let (cb', logNotes) = foldl replay (cb, []) (zip [1 :: Int ..] logLines)
  pure (cb', decodeNotes ++ enterNotes ++ reverse logNotes)
 where
  readType file = verifyType file <$> BS.readFile (store.dir </> "types" </> file)
  readTerm file = verifyTerm file <$> BS.readFile (store.dir </> "terms" </> file)

  -- Dependencies first; a term is skipped, with a note, if it does not check.
  enterAll :: Map Hash (Term Z) -> Codebase -> (Codebase, [Text])
  enterAll loaded cb0 =
    let (cb, _, notes) = foldl visit (cb0, Set.empty, []) (Map.keys loaded)
     in (cb, reverse notes)
   where
    visit st@(cb, seen, notes) h
      | Set.member h seen || Map.member h cb.terms = st
      | Just t <- Map.lookup h loaded =
          let (cb', seen', notes') = foldl visit (cb, Set.insert h seen, notes) (Set.toList (refs t))
           in case storeTerm h t cb' of
                Right cb'' -> (cb'', seen', notes')
                Left err ->
                  ( cb'
                  , seen'
                  , ("terms/" <> hashHex h <> ": does not typecheck (" <> err <> "), skipped")
                      : notes'
                  )
      | otherwise = st

  replay (cb, notes) (lineNo, line) = case T.words line of
    [_, "bind", name, target]
      | Just r <- parseRef target ->
          if Map.member r.hash cb.terms
            then (bindName name r cb, notes)
            else
              ( cb
              , ( "names.log:"
                    <> tshow lineNo
                    <> ": "
                    <> name
                    <> " points at a missing term, skipped"
                )
                  : notes
              )
    [_, "unname", name] -> (unbindName name cb, notes)
    -- Declared types and their constructors (design §7.4).
    [_, "type", name, hex]
      | Just h <- hashFromHex hex ->
          if Map.member h cb.typeDefs
            then (bindTypeName name h cb, notes)
            else
              ( cb
              , ("names.log:" <> tshow lineNo <> ": " <> name <> " names a missing type, skipped")
                  : notes
              )
    [_, "con", name, target]
      | Just (Reference h (Just i)) <- parseRef target ->
          if Map.member h cb.typeDefs
            then (bindConName name h i cb, notes)
            else
              ( cb
              , ( "names.log:"
                    <> tshow lineNo
                    <> ": "
                    <> name
                    <> " names a constructor of a missing type, skipped"
                )
                  : notes
              )
    [_, "field", name, target]
      | [hex, i, j] <- T.splitOn "." target
      , Just h <- hashFromHex hex
      , [(i', "")] <- reads (T.unpack i)
      , [(j', "")] <- reads (T.unpack j) ->
          if Map.member h cb.typeDefs
            then (bindFieldName name h i' j' cb, notes)
            else
              ( cb
              , ( "names.log:"
                    <> tshow lineNo
                    <> ": "
                    <> name
                    <> " names a field of a missing type, skipped"
                )
                  : notes
              )
    -- Units and charts are names (design §3.2.12).
    [_, "unit", name] -> (markUnit name cb, notes)
    [_, "chart", name] -> (markChart name cb, notes)
    -- A `let` that rebinds a unit or chart name makes it a plain quantity (design §3.2.12).
    [_, "unflag", name] -> (clearFlags name cb, notes)
    (_ : "prefer" : rest) -> (addPreference (T.unwords rest) cb, notes)
    (_ : "unprefer" : rest) -> (removePreference (T.unwords rest) cb, notes)
    -- The codebase's stored default uses (design §7.7).
    (_ : "use" : rest) | Just u <- parseUse rest -> (addStoredUse u cb, notes)
    (_ : "unuse" : rest) | Just u <- parseUse rest -> (removeStoredUse u cb, notes)
    -- Signatures (design §4.8).
    (_ : "sig" : name : rest@(_ : _)) -> case replaySignature name (T.unwords rest) cb of
      Right cb' -> (cb', notes)
      Left why ->
        ( cb
        , ( "names.log:"
              <> tshow lineNo
              <> ": the signature of "
              <> name
              <> " cannot be read back ("
              <> why
              <> "), skipped"
          )
            : notes
        )
    [_, "unsig", name] -> (dropSignature name cb, notes)
    [] -> (cb, notes)
    _ -> (cb, ("names.log:" <> tshow lineNo <> ": unreadable line, skipped") : notes)

{- | Write what changed between two codebases: new terms (with every term they
reference, so the store stays self-contained), then name and unit changes
to the log. Terms are written before the log lines that point at them, and
dependencies before dependents, so an interrupted write never leaves a name
pointing at a missing term.
-}
sync :: Store -> Codebase -> Codebase -> IO ()
sync store old new = do
  writeContent store old new
  now <- (round <$> getPOSIXTime) :: IO Integer
  let entries = logEntries (tshow now) old new
  unless (null entries)
    $ TIO.appendFile (store.dir </> "names.log") (T.unlines entries)

{- | The type and term files for what one codebase has and another lacks,
each term after the terms it references.
-}
writeContent :: Store -> Codebase -> Codebase -> IO ()
writeContent store old new = do
  forM_ (Map.toList (Map.difference new.typeDefs old.typeDefs)) $ \(h, def) ->
    BS.writeFile
      (store.dir </> "types" </> T.unpack (hashHex h))
      (encodeTypeDef def)
  let fresh = Map.keys (Map.difference new.terms old.terms)
  foldM_ writeClosure Set.empty fresh
 where
  writeClosure :: Set Hash -> Hash -> IO (Set Hash)
  writeClosure written h
    | Set.member h written = pure written
    | otherwise = do
        let path = store.dir </> "terms" </> T.unpack (hashHex h)
        present <- doesFileExist path
        case Map.lookup h new.terms of
          Just t | not present -> do
            written' <- foldM writeClosure (Set.insert h written) (Set.toList (refs t))
            BS.writeFile path (encodeStored t)
            pure written'
          _ -> pure (Set.insert h written)

-- | The log lines that take one codebase's labels to another's, at a time.
logEntries :: Text -> Codebase -> Codebase -> [Text]
logEntries stamp old new =
  let binds =
        [ stamp <> " bind " <> name <> " " <> refText r
        | (name, r) <- Map.toList new.names
        , Map.lookup name old.names /= Just r
        ]
      -- A name a bind or con line of this sync takes over needs no unname.
      gone name =
        not
          ( Map.member name new.names
              || Map.member name new.conNames
              || Map.member name new.typeNames
          )
      unnames =
        [ stamp <> " unname " <> name
        | name <- Map.keys (Map.difference old.names new.names)
        , gone name
        ]
      units =
        [stamp <> " unit " <> n | n <- Set.toList (Set.difference new.units old.units)]
      charts =
        [ stamp <> " chart " <> n | n <- Set.toList (Set.difference new.charts old.charts)
        ]
      -- A flag a name lost while it stays bound; an unnamed label needs no line.
      unflags =
        [ stamp <> " unflag " <> n
        | n <-
            Set.toList
              ( Set.union
                  (Set.difference old.units new.units)
                  (Set.difference old.charts new.charts)
              )
        , Map.member n new.names
        ]
      prefers =
        [ stamp <> " prefer " <> t
        | t <- Set.toList (Set.difference new.preferences old.preferences)
        ]
      unprefers =
        [ stamp <> " unprefer " <> t
        | t <- Set.toList (Set.difference old.preferences new.preferences)
        ]
      types =
        [ stamp <> " type " <> name <> " " <> hashHex h
        | (name, h) <- Map.toList new.typeNames
        , Map.lookup name old.typeNames /= Just h
        ]
      cons =
        [ stamp <> " con " <> name <> " " <> hashHex h <> "." <> tshow i
        | (name, (h, i)) <- Map.toList new.conNames
        , Map.lookup name old.conNames /= Just (h, i)
        ]
      fields =
        [ stamp
            <> " field "
            <> name
            <> " "
            <> hashHex h
            <> "."
            <> tshow i
            <> "."
            <> tshow j
        | (name, (h, i, j)) <- Map.toList new.fieldNames
        , Map.lookup name old.fieldNames /= Just (h, i, j)
        ]
      -- A field label is unnamed with its dot.
      unnamedFields =
        [ stamp <> " unname ." <> name
        | name <- Map.keys (Map.difference old.fieldNames new.fieldNames)
        ]
      -- An unname line covers a type or constructor label as well.
      unnamedTypes =
        [ stamp <> " unname " <> name
        | name <-
            Map.keys (Map.difference old.typeNames new.typeNames)
              ++ Map.keys (Map.difference old.conNames new.conNames)
        , gone name
        ]
      -- The stored default uses (design §7.7).
      unuses = [stamp <> " unuse " <> renderUse u | u <- old.uses, u `notElem` new.uses]
      uses = [stamp <> " use " <> renderUse u | u <- new.uses, u `notElem` old.uses]
      -- Signatures (design §4.8), written as they read back at the root, last:
      -- after the labels and uses they are read with.
      sigs =
        [ stamp <> " sig " <> name <> " " <> signatureLogText new sig
        | (name, sig) <- Map.toList new.signatures
        , Map.lookup name old.signatures /= Just sig
        ]
      -- Also for a name that lost its label, though its unname takes the
      -- signature too: the log says what happened to it.
      unsigs =
        [ stamp <> " unsig " <> name
        | name <- Map.keys (Map.difference old.signatures new.signatures)
        ]
   in types
        ++ cons
        ++ fields
        ++ binds
        ++ unnames
        ++ unnamedTypes
        ++ unnamedFields
        ++ units
        ++ charts
        ++ prefers
        ++ unprefers
        ++ unflags
        ++ unuses
        ++ uses
        ++ unsigs
        ++ sigs

{- | A signature as its log line spells it (design §7.4, §4.8): ASCII, the
variables named so that they read back as variables at the root, and
declared types by their absolute paths, so that the stored @use@s cannot
change what the text means.
-}
signatureLogText :: Codebase -> Scheme -> Text
signatureLogText cb =
  renderSignature
    Ascii
    (\h -> maybe (showHash h) ("." <>) (typeNameOf h cb))

{- | A signature line read back: the type parsed and converted at the root
as a written signature is, for a name that is bound and whose definition
it holds of.
-}
replaySignature :: Text -> Text -> Codebase -> Either Text Codebase
replaySignature name text cb = do
  t <- parseType text
  sig <-
    either
      (Left . renderResolveError)
      (Right . fst)
      (signatureScheme rootScope cb t)
  case lookupName name cb >>= (`typeOf` cb) of
    Just general
      | signatureHolds sig general -> Right (setSignature name sig cb)
      | otherwise -> Left "the signature does not hold of the definition"
    Nothing -> Left "the name is not bound"

-- | A stored use as its log line spells it: @std@, @orbital as o@.
parseUse :: [Text] -> Maybe Use
parseUse = \case
  [p] -> Just (Use p Nothing)
  [p, "as", a] -> Just (Use p (Just a))
  _ -> Nothing

-- | A type file's content, checked against the hash that names it.
verifyType :: FilePath -> BS.ByteString -> Either Text (Hash, TypeDef)
verifyType file raw = case hashFromHex (T.pack file) of
  Nothing -> Left ("types/" <> T.pack file <> ": not a hash, ignored")
  Just h -> case decodeTypeDef raw of
    Left err -> Left ("types/" <> T.pack file <> ": " <> err <> ", ignored")
    Right def
      | hashTypeDef def /= h ->
          Left ("types/" <> T.pack file <> ": content does not match its hash, ignored")
      | otherwise -> Right (h, def)

-- | A term file's content, checked against the hash that names it.
verifyTerm :: FilePath -> BS.ByteString -> Either Text (Hash, Term Z)
verifyTerm file raw = case hashFromHex (T.pack file) of
  Nothing -> Left ("terms/" <> T.pack file <> ": not a hash, ignored")
  Just h -> case decodeStored raw of
    Left err -> Left ("terms/" <> T.pack file <> ": " <> err <> ", ignored")
    Right t
      | hashTerm t /= h ->
          Left ("terms/" <> T.pack file <> ": content does not match its hash, ignored")
      | otherwise -> Right (h, t)

-- | What a merge brought across, and anything it skipped or noticed.
data MergeReport = MergeReport
  { termsCopied :: Int
  , typesCopied :: Int
  , linesAdded :: Int
  , notes :: [Text]
  }
  deriving (Eq, Show)

{- | Merge the store at the second path into the store at the first (design
§7.4). The target is opened as 'openStore' does, so it is created and seeded if
missing; the source must already be a store of the current format, and is
only read. A store of another format, either one, is refused (design §7.4).
-}
mergeStores ::
  Either Text Seed -> FilePath -> FilePath -> IO (Either Text MergeReport)
mergeStores seed target source = do
  isDir <- doesDirectoryExist source
  hasFormat <- doesFileExist (source </> "format")
  same <- (==) <$> canonicalizePath target <*> canonicalizePath source
  if not isDir
    then pure (Left (T.pack source <> ": no such directory"))
    else
      if not hasFormat
        then
          pure
            (Left (T.pack source <> " is not an eval codebase (it has no format file)"))
        else
          if same
            then pure (Left (T.pack source <> ": a store cannot be merged into itself"))
            else do
              -- The source first: if it is refused, the target is not touched.
              openedSource <- openStore seed source
              openedTarget <-
                either (pure . Left) (const (openStore seed target)) openedSource
              case (,) <$> openedSource <*> openedTarget of
                Left err -> pure (Left err)
                Right (src, dst) -> Right <$> mergeStore dst src

{- | Merge one open store into another; the source is only read.

Types and terms the target lacks are copied, each checked against its hash
first as 'loadStore' does. A file of the same name is the same content, so
nothing is overwritten. Then the logs are merged: the source's lines that
the target already has are dropped (once for each copy the target has, so
merging again adds nothing), the rest are appended, and the whole log is
stably sorted by its leading time, so replay gives the last writer per name.
On a tie the target's line comes first and the source's wins. A line with
no readable time sorts as if at time 0 and is reported. The log is written
last, through a temporary file, so an interrupted merge never leaves a name
pointing at a missing term or a truncated log. The REPL @history@ file is
the target's own and is neither copied nor touched.
-}
mergeStore :: Store -> Store -> IO MergeReport
mergeStore target source = do
  (types, typeNotes) <- copyVerified "types" (\f raw -> void (verifyType f raw))
  (terms, termNotes) <- copyVerified "terms" (\f raw -> void (verifyTerm f raw))
  (added, logNotes) <- mergeLogs
  pure
    MergeReport
      { termsCopied = terms
      , typesCopied = types
      , linesAdded = added
      , notes = typeNotes ++ termNotes ++ logNotes
      }
 where
  copyVerified ::
    FilePath -> (FilePath -> BS.ByteString -> Either Text ()) -> IO (Int, [Text])
  copyVerified sub verify = do
    let from = source.dir </> sub
        to = target.dir </> sub
    present <- doesDirectoryExist from
    files <- if present then listDirectory from else pure []
    results <-
      mapM
        ( \file -> do
            have <- doesPathExist (to </> file)
            isFile <- doesFileExist (from </> file)
            if have || not isFile
              then pure (Right False)
              else do
                raw <- BS.readFile (from </> file)
                case verify file raw of
                  Left err -> pure (Left (T.pack source.dir <> ": " <> err))
                  Right () -> do
                    let tmp = target.dir </> "merge.tmp"
                    BS.writeFile tmp raw
                    renameFile tmp (to </> file)
                    pure (Right True)
        )
        files
    pure (length (filter id (rights results)), lefts results)

  mergeLogs :: IO (Int, [Text])
  mergeLogs = do
    let logFile = target.dir </> "names.log"
    present <- doesFileExist logFile
    old <- if present then TIO.readFile logFile else pure ""
    theirsPresent <- doesFileExist (source.dir </> "names.log")
    theirs <-
      if theirsPresent
        then numbered <$> TIO.readFile (source.dir </> "names.log")
        else pure []
    let mine = numbered old
        known = Map.fromListWith (+) [(l, 1 :: Int) | (_, l) <- mine]
        fresh = dropKnown known theirs
        merged = sortOn (fromMaybe 0 . stampOf) (map snd mine ++ map snd fresh)
        new = T.unlines merged
    when (new /= old) $ do
      let tmp = target.dir </> "names.log.merge"
      TIO.writeFile tmp new
      renameFile tmp logFile
    pure (length fresh, unstamped target.dir mine ++ unstamped source.dir fresh)

  -- Blank lines carry nothing and are dropped.
  numbered = filter (not . T.null . T.strip . snd) . zip [1 :: Int ..] . T.lines

  dropKnown _ [] = []
  dropKnown known (x@(_, l) : rest) = case Map.lookup l known of
    Just k | k > 0 -> dropKnown (Map.insert l (k - 1) known) rest
    _ -> x : dropKnown known rest

  unstamped d ls =
    [ T.pack d
        <> "/names.log:"
        <> tshow n
        <> ": no time at the start of the line, sorted to the beginning"
    | (n, l) <- ls
    , Nothing <- [stampOf l]
    ]

  stampOf :: Text -> Maybe Integer
  stampOf l = case T.words l of
    w : _ | Right (t, "") <- TR.decimal w -> Just t
    _ -> Nothing

refText :: Reference -> Text
refText r = hashHex r.hash <> maybe "" (\i -> "." <> tshow i) r.index

parseRef :: Text -> Maybe Reference
parseRef t = case T.splitOn "." t of
  [hex] -> (`Reference` Nothing) <$> hashFromHex hex
  [hex, i] | [(n, "")] <- reads (T.unpack i) -> (`Reference` Just n) <$> hashFromHex hex
  _ -> Nothing

tshow :: (Show a) => a -> Text
tshow = T.pack . show
