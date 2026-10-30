{- | The codebase on disk (design §7.4).

A store is a directory:

@
format          "eval codebase 1"
terms\/\<hex\>    one term per file, in the storage encoding ("Eval.Hash")
types\/\<hex\>    one declared type per file (design §6.1)
names.log       append-only: time, then  bind name ref | unname name | unit name | scale name | prefer text | unprefer text | type name hex | con name hex.i | field name hex.i.j
@

Terms are content-addressed, so they never conflict and are only ever
added. Everything label-level (names, their history, unit declarations) is
the log replayed in order, which is also what makes two stores mergeable:
concatenate the logs and sort by time, which is what 'mergeStore' does.

The prelude is not stored as bindings. Every session enters it first, in
memory, and the store's log is replayed on top, so a user who rebinds a
prelude name keeps that binding and a prelude that changes a definition
leaves the user's dependents pointing at the old hash, visible in @:todo@.
Prelude /terms/ that a stored definition references are written beside it,
so a store is self-contained whatever the prelude later becomes.
-}
module Eval.Store (
  Store (..),
  formatVersion,
  locateStore,
  openStore,
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
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Text.Read qualified as TR
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Codebase
import Eval.Core
import Eval.Hash
import Eval.Resolve (storeTerm)
import Eval.Type (TypeDef)
import System.Directory
import System.FilePath

newtype Store = Store {dir :: FilePath}

formatLine :: Int -> Text
formatLine v = "eval codebase " <> tshow v

-- | Bumped whenever the storage encoding changes; see core.md on hash stability.
formatVersion :: Int
formatVersion = storageVersion

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

-- | Create the directory if needed, or check that an existing one is ours.
openStore :: FilePath -> IO (Either Text Store)
openStore d = do
  createDirectoryIfMissing True (d </> "terms")
  createDirectoryIfMissing True (d </> "types")
  let formatFile = d </> "format"
  present <- doesFileExist formatFile
  if not present
    then do
      TIO.writeFile formatFile (formatLine formatVersion <> "\n")
      pure (Right (Store d))
    else do
      line <- T.strip <$> TIO.readFile formatFile
      if line == formatLine formatVersion
        then pure (Right (Store d))
        else
          if line == formatLine (1 :: Int)
            then migrate1to2 >> migrate2to3 >> pure (Right (Store d))
            else
              if line == formatLine (2 :: Int)
                then migrate2to3 >> pure (Right (Store d))
                else
                  pure
                    ( Left
                        ( T.pack d
                            <> " is not an eval codebase of format "
                            <> tshow formatVersion
                            <> " (found \""
                            <> line
                            <> "\"); see core.md on migrations"
                        )
                    )
 where
  -- Format 2 added the written name after each reference (design §7.4).
  -- Hashes are unchanged, so every term file is rewritten in place with
  -- empty hints and the log is kept; the loader reads its unit lines by
  -- reference as well as by name.
  migrate1to2 = do
    files <- listDirectory (d </> "terms")
    mapM_
      ( \file -> do
          raw <- BS.readFile (d </> "terms" </> file)
          case decodeStoredV 1 raw of
            Right t -> BS.writeFile (d </> "terms" </> file) (encodeStored t)
            Left _ -> pure ()
      )
      files
    TIO.writeFile (d </> "format") (formatLine (2 :: Int) <> "\n")
  -- Format 3 replaced If and the boolean literal by Case and Con, which
  -- changes hashes: every term is decoded by the format-2 rules (the decoder
  -- rewrites those forms), re-hashed with its references mapped to the new
  -- hashes in dependency order, and the log's bind lines are rewritten.
  migrate2to3 = do
    files <- listDirectory (d </> "terms")
    decoded <-
      mapM
        ( \file -> do
            raw <- BS.readFile (d </> "terms" </> file)
            pure $ case (hashFromHex (T.pack file), decodeStoredV 2 raw) of
              (Just h, Right t) -> Just (h, t)
              _ -> Nothing
        )
        files
    let old = Map.fromList (catMaybes decoded)
        visit acc h
          | Map.member h acc = acc
          | Just t <- Map.lookup h old =
              let acc' = foldl visit acc (Set.toList (refs t))
                  t' = rewriteRefs (\h' i -> (\(new, _) -> (new, i)) <$> Map.lookup h' acc') t
               in Map.insert h (hashTerm t', t') acc'
          | otherwise = acc
        remap = foldl visit Map.empty (Map.keys old)
        newHashes = Set.fromList [h' | (h', _) <- Map.elems remap]
    forM_ (Map.toList remap) $ \(h, (h', t')) -> do
      BS.writeFile (d </> "terms" </> T.unpack (hashHex h')) (encodeStored t')
      when (h' /= h && not (Set.member h newHashes))
        $ removeFile (d </> "terms" </> T.unpack (hashHex h))
    let logFile = d </> "names.log"
    present <- doesFileExist logFile
    when present $ do
      ls <- T.lines <$> TIO.readFile logFile
      let hexMap = Map.fromList [(hashHex h, hashHex h') | (h, (h', _)) <- Map.toList remap]
          fixWord w = case T.splitOn "." w of
            (hex : rest) | Just new <- Map.lookup hex hexMap -> T.intercalate "." (new : rest)
            _ -> w
      TIO.writeFile logFile (T.unlines (map (T.unwords . map fixWord . T.words) ls))
    TIO.writeFile (d </> "format") (formatLine formatVersion <> "\n")

{- | Load the store on top of a codebase (the prelude's): decode every term,
check and add them dependencies first, then replay the log. Problems are
reported as notes and the rest still loads.
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
    -- Units and scales are names (design §3.2.12). A format-1 log flagged a
    -- reference; every name then bound to it is flagged.
    [_, "unit", target] -> (flagNames markUnit target cb, notes)
    [_, "scale", target] -> (flagNames markScale target cb, notes)
    (_ : "prefer" : rest) -> (addPreference (T.unwords rest) cb, notes)
    (_ : "unprefer" : rest) -> (removePreference (T.unwords rest) cb, notes)
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
  forM_ (Map.toList (Map.difference new.typeDefs old.typeDefs)) $ \(h, def) ->
    BS.writeFile
      (store.dir </> "types" </> T.unpack (hashHex h))
      (encodeTypeDef def)
  let fresh = Map.keys (Map.difference new.terms old.terms)
  foldM_ writeClosure Set.empty fresh
  now <- (round <$> getPOSIXTime) :: IO Integer
  let stamp = tshow now
      binds =
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
      scales =
        [ stamp <> " scale " <> n | n <- Set.toList (Set.difference new.scales old.scales)
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
      entries =
        types
          ++ cons
          ++ fields
          ++ binds
          ++ unnames
          ++ unnamedTypes
          ++ unnamedFields
          ++ units
          ++ scales
          ++ prefers
          ++ unprefers
  unless (null entries)
    $ TIO.appendFile (store.dir </> "names.log") (T.unlines entries)
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
§7.4). The target is opened as 'openStore' does, so it is created if
missing; the source must already be a store and is only read, apart from a
migration to the current format on open, which the notes mention.
-}
mergeStores :: FilePath -> FilePath -> IO (Either Text MergeReport)
mergeStores target source = do
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
              sourceWas <- formatOf source
              openedSource <- openStore source
              targetWas <- formatOf target
              openedTarget <- either (pure . Left) (const (openStore target)) openedSource
              case (,) <$> openedSource <*> openedTarget of
                Left err -> pure (Left err)
                Right (src, dst) -> do
                  report <- mergeStore dst src
                  pure
                    ( Right
                        report
                          { notes =
                              migrated source sourceWas
                                ++ migrated target targetWas
                                ++ report.notes
                          }
                    )
 where
  formatOf d = do
    present <- doesFileExist (d </> "format")
    if not present
      then pure Nothing
      else do
        line <- T.strip <$> TIO.readFile (d </> "format")
        pure $ case TR.decimal <$> T.stripPrefix "eval codebase " line of
          Just (Right (v, "")) -> Just (v :: Int)
          _ -> Nothing
  migrated d = \case
    Just v
      | v /= formatVersion ->
          [ T.pack d
              <> " was migrated in place from format "
              <> tshow v
              <> " to "
              <> tshow formatVersion
          ]
    _ -> []

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

flagNames :: (Text -> Codebase -> Codebase) -> Text -> Codebase -> Codebase
flagNames mark target cb = case parseRef target of
  Just r -> foldr mark cb (namesOf r cb)
  Nothing -> mark target cb

refText :: Reference -> Text
refText r = hashHex r.hash <> maybe "" (\i -> "." <> tshow i) r.index

parseRef :: Text -> Maybe Reference
parseRef t = case T.splitOn "." t of
  [hex] -> (`Reference` Nothing) <$> hashFromHex hex
  [hex, i] | [(n, "")] <- reads (T.unpack i) -> (`Reference` Just n) <$> hashFromHex hex
  _ -> Nothing

tshow :: (Show a) => a -> Text
tshow = T.pack . show
