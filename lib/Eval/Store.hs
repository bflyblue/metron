{- | The codebase on disk (design §7.4).

A store is a directory:

@
format          "eval codebase 6"
terms\/\<hex\>    one term per file, in the storage encoding ("Eval.Hash")
types\/\<hex\>    one declared type per file (design §6.1)
names.log       append-only: time, then  bind name ref | unname name | unit name | scale name | prefer text | unprefer text | type name hex | con name hex.i | field name hex.i.j | use path [as alias] | unuse path [as alias] | sig name type | unsig name
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
the empty codebase; nothing is entered in memory first.
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

import Control.Monad (filterM, foldM, foldM_, forM_, unless, void, when)
import Data.ByteString qualified as BS
import Data.Either (lefts, rights)
import Data.List (nub, sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Text.Read qualified as TR
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Builtin (boolHash, builtinDefs, listHash, pairHash)
import Eval.Codebase
import Eval.Core
import Eval.Dimension (Spelling (..))
import Eval.Hash
import Eval.Parser (parseType)
import Eval.Prelude (
  stdlib4Codebase,
  stdlib4Moved,
  stdlibCodebase,
  stdlibHomes,
  stdlibMoved,
 )
import Eval.Resolve (queryScheme, renderResolveError, storeTerm, typeVariable)
import Eval.Syntax (Use (..), renderUse, rootScope)
import Eval.TCore (signatureHolds)
import Eval.Type (Arg (..), Scheme, Type (..), TypeDef (..), renderSignature)
import Eval.Update (restampTerm, retypeType)
import System.Directory
import System.FilePath

newtype Store = Store {dir :: FilePath}

formatLine :: Int -> Text
formatLine v = "eval codebase " <> tshow v

{- | Bumped whenever the store's layout changes: the storage encoding
('storageVersion', 4), or what a store holds. Format 4 holds the standard
library as seeded labels instead of assuming a prelude entered in memory
(design §7.7); format 5 holds it split by domain into sibling namespaces
and re-seeds a format-4 store; format 6 (storage version 4) holds @Bool@,
tuples and lists as declared types, re-hashing what uses them. See
core.md on hash stability and migrations.
-}
formatVersion :: Int
formatVersion = 6

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

{- | What a new store is seeded with (design §7.7), and what an older store
is migrated with: the library's codebase, with its stored @use@s, and the
earlier references of its names; and the format-4 library, everything
under @std@, with the references the old root prelude gave its names
where the move under @std@ changed them (the definitions whose @±@ is
stamped with their name, design §3.2.4, and those that use them).
-}
data Seed = Seed
  { library :: Codebase
  , moved :: [(Text, Reference)]
  -- ^ @si.km@ and the reference @std.km@ had, oldest first (design §7.4)
  , homes :: [(Text, Text)]
  -- ^ each format-4 library name and its home now: @std.km@, @si.km@
  , library4 :: Codebase
  -- ^ the format-4 library, for the 3 to 4 and 4 to 5 migrations
  , moved4 :: [(Text, Reference)]
  -- ^ @std.G@ and the reference the root @G@ had
  }

-- | The standard library as a 'Seed'.
stdlibSeed :: Either Text Seed
stdlibSeed =
  Seed
    <$> stdlibCodebase
    <*> stdlibMoved
    <*> stdlibHomes
    <*> stdlib4Codebase
    <*> stdlib4Moved

{- | Create the directory if needed and seed it, or check that an existing
one is ours, migrating an older format in place. The seed is only looked
at to create or migrate a store, so opening a current one never enters
the library in memory: the store has it.
-}
openStore :: Either Text Seed -> FilePath -> IO (Either Text Store)
openStore seeding d = do
  createDirectoryIfMissing True (d </> "terms")
  createDirectoryIfMissing True (d </> "types")
  let formatFile = d </> "format"
  present <- doesFileExist formatFile
  if not present
    then withSeed $ \seed -> do
      -- The format file last, so an interrupted seeding is seeded again.
      seedStore (Store d) seed.library
      TIO.writeFile formatFile (formatLine formatVersion <> "\n")
    else do
      line <- T.strip <$> TIO.readFile formatFile
      if line == formatLine formatVersion
        then pure (Right (Store d))
        else case [v | v <- [1 .. formatVersion - 1], line == formatLine v] of
          -- Each step takes the store one format on and says so in its format
          -- file, so an interrupted chain resumes where it stopped.
          [v] -> withSeed (\seed -> mapM_ ($ seed) (drop (v - 1) steps))
          _ ->
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
  -- The library steps compare the store with the library as this build
  -- enters it, so the store's terms and types are brought to format 6's
  -- hashes first ('retireBuiltins', which changes nothing the second time).
  steps =
    [ const migrate1to2
    , const migrate2to3
    , \seed -> retireBuiltins d >> migrate3to4 seed
    , \seed -> retireBuiltins d >> migrate4to5 seed
    , \seed -> retireBuiltins d >> migrate5to6 seed
    ]
  withSeed k = case seeding of
    Left err -> pure (Left ("the standard library does not load:\n" <> err))
    Right seed -> k seed >> pure (Right (Store d))
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
    TIO.writeFile (d </> "format") (formatLine (3 :: Int) <> "\n")
  -- Format 4 holds the standard library instead of assuming a prelude
  -- entered in memory under every session (design §7.4, §7.7). The store is
  -- seeded as a new one is, before its own log, so a user's root binding
  -- that shadows a library name still wins. Where the move under `std`
  -- changed a reference (a `±` is stamped with the full path, so `std.G`
  -- is not the root `G`) and a user term still uses the old one, whose file
  -- the store therefore holds, the name's history gets the old reference
  -- first, so `:todo` reports the user's term as stale and `:upgrade std.G`
  -- moves it. The current one is bound again at time 1, so a merge with a
  -- store seeded fresh, whose time-0 lines sort first, ends on it too.
  -- The library of format 4 is the one seeded here, everything under `std`;
  -- the 4 to 5 step that follows replaces it.
  migrate3to4 seed = do
    old <- filterM (hasTerm . snd) seed.moved4
    let current = [(n, r) | (n, _) <- old, Just r <- [lookupName n seed.library4]]
        history = [seedStamp <> " bind " <> n <> " " <> refText r | (n, r) <- old]
        rebound = ["1 bind " <> n <> " " <> refText r | (n, r) <- current]
    seedStoreWith history rebound id (Store d) seed.library4
    TIO.writeFile (d </> "format") (formatLine (4 :: Int) <> "\n")
  -- Format 5 splits the library by domain into sibling namespaces (design
  -- §7.7), and `km` is written `kilo * metre`, so most library hashes
  -- changed: the store is re-seeded. Every label still on the binding the
  -- format-4 library gave it is removed, with every log line that names
  -- it; a label the user rebound or added is kept. The stored `use std` is
  -- replaced by the new library's six, unless the user had removed it. The
  -- new library is seeded before the log, as a new store is, and each
  -- removed name's earlier references (the format-4 `std.km`, and before
  -- it the root prelude's where the move under `std` changed it) go first
  -- into the history of its new home, so `:todo` reports a user term that
  -- still uses one as stale and `:upgrade si.km` moves it. The current
  -- reference is bound again at time 1, as in the 3 to 4 step.
  migrate4to5 seed = do
    (cb, _) <- loadStore (Store d) emptyCodebase
    let still :: (Eq v) => (Codebase -> Map Text v) -> Set Text
        still field =
          Map.keysSet
            ( Map.filterWithKey
                (\n v -> Map.lookup n (field cb) == Just v)
                (field seed.library4)
            )
        gone = Set.unions [still (.names), still (.typeNames), still (.conNames)]
        goneFields = still (.fieldNames)
        names n =
          Set.member n gone || maybe False (`Set.member` goneFields) (T.stripPrefix "." n)
        dropped l = case T.words l of
          [_, kw, "std"] -> kw `elem` ["use", "unuse"]
          [_, kw, n] -> kw `elem` ["unname", "unit", "scale", "unflag"] && names n
          [_, "field", n, _] -> Set.member n goneFields
          [_, kw, n, _] -> kw `elem` ["bind", "type", "con"] && Set.member n gone
          _ -> False
        library
          | Use "std" Nothing `elem` cb.uses = seed.library
          | otherwise = seed.library{uses = []}
    earlier <-
      filterM
        (hasTerm . snd)
        ( nub
            [ (h, r)
            | (o, h) <- seed.homes
            , Set.member o gone
            , (h', r) <- seed.moved
            , h' == h
            ]
        )
    let current =
          nub [(h, r) | (h, _) <- earlier, Just r <- [lookupName h seed.library]]
        history = [seedStamp <> " bind " <> n <> " " <> refText r | (n, r) <- earlier]
        rebound = ["1 bind " <> n <> " " <> refText r | (n, r) <- current]
    seedStoreWith
      history
      rebound
      (T.unlines . filter (not . dropped) . T.lines)
      (Store d)
      library
    TIO.writeFile (d </> "format") (formatLine (5 :: Int) <> "\n")
  -- Format 6 made Bool, tuples and lists declarations the compiler holds
  -- (design §7.4, §7.7). 'retireBuiltins' has re-hashed the store; what is
  -- left is the library's labels for the three types, which a format-5
  -- library did not have: their type files are written and their type and
  -- constructor lines go first in the log, at time 0 as the seed's do, for
  -- every such label the store does not bind already (a store re-seeded by
  -- the 4 to 5 step has them).
  migrate5to6 seed = do
    (cb, _) <- loadStore (Store d) emptyCodebase
    let builtin h = isJust (builtinDefs h)
        typeLines =
          [ seedStamp <> " type " <> n <> " " <> hashHex h
          | (n, h) <- Map.toList seed.library.typeNames
          , builtin h
          , Map.notMember n cb.typeNames
          ]
        conLines =
          [ seedStamp <> " con " <> n <> " " <> hashHex h <> "." <> tshow i
          | (n, (h, i)) <- Map.toList seed.library.conNames
          , builtin h
          , Map.notMember n cb.conNames
          ]
    forM_ [boolHash, pairHash, listHash] $ \h ->
      forM_ (builtinDefs h) $ \def ->
        BS.writeFile (d </> "types" </> T.unpack (hashHex h)) (encodeTypeDef def)
    let logFile = d </> "names.log"
    present <- doesFileExist logFile
    old <- if present then TIO.readFile logFile else pure ""
    TIO.writeFile (logFile <> ".seed") (T.unlines (typeLines ++ conLines) <> old)
    renameFile (logFile <> ".seed") logFile
    TIO.writeFile (d </> "format") (formatLine (6 :: Int) <> "\n")
  hasTerm r = doesFileExist (d </> "terms" </> T.unpack (hashHex r.hash))

{- | Bring a store of format 3 to 5 to format 6's hashes (design §7.4):
@Bool@, tuples and lists were built into the type language and Core
(type tags 0x20, 0x24, 0x25, constructors by name) and are now declared
types on the hashes of "Eval.Builtin". Every type file is read by the old
rules, which read those forms as the declared ones, and re-hashed, types
before the types whose fields use them; then every term, its constructors
moved to the re-hashed types and its references to the re-hashed terms,
dependencies first, as the 2 to 3 step did; the files are written under
their new hashes and the old ones removed; and every hash in the log is
replaced by its new one, which carries the labels, their history, the
units and the constructors and fields across. Signature lines name types
by path, so they need nothing. A store already at format 6's hashes reads
back unchanged, so this may run more than once.

A cycle keeps its members in the order their old placeholder hashes gave
them; the same source entered again may order them otherwise, and so be
a different term, as with any change of encoding (core.md §6).
-}
retireBuiltins :: FilePath -> IO ()
retireBuiltins d = do
  typeFiles <- listDirectory (d </> "types")
  oldTypes <-
    Map.fromList . catMaybes
      <$> mapM
        ( \file -> do
            raw <- BS.readFile (d </> "types" </> file)
            pure $ case (hashFromHex (T.pack file), decodeTypeDefV 3 raw) of
              (Just h, Right def) -> Just (h, def)
              _ -> Nothing
        )
        typeFiles
  -- A type's hash covers its fields', so the types form no cycle.
  let visitType acc h
        | Map.member h acc = acc
        | Just def <- Map.lookup h oldTypes =
            let acc' =
                  foldl visitType acc (Set.toList (foldMap (foldMap typeHashes) def.constructors))
                def' =
                  def{constructors = map (map (retypeType (Map.map fst acc'))) def.constructors}
             in Map.insert h (hashTypeDef def', def') acc'
        | otherwise = acc
      types = foldl visitType Map.empty (Map.keys oldTypes)
      typeMap = Map.map fst types
      con (UserCon h i) = UserCon (Map.findWithDefault h h typeMap) i
  termFiles <- listDirectory (d </> "terms")
  oldTerms <-
    Map.fromList . catMaybes
      <$> mapM
        ( \file -> do
            raw <- BS.readFile (d </> "terms" </> file)
            pure $ case (hashFromHex (T.pack file), decodeStoredV 3 raw) of
              (Just h, Right t) -> Just (h, t)
              _ -> Nothing
        )
        termFiles
  let visitTerm acc h
        | Map.member h acc = acc
        | Just t <- Map.lookup h oldTerms =
            let acc' = foldl visitTerm acc (Set.toList (refs t))
                t' =
                  rewriteRefs
                    (\h' i -> (\(new, _) -> (new, i)) <$> Map.lookup h' acc')
                    (restampTerm id con t)
             in Map.insert h (hashTerm t', t') acc'
        | otherwise = acc
      terms = foldl visitTerm Map.empty (Map.keys oldTerms)
  rewrite "types" encodeTypeDef types
  rewrite "terms" encodeStored terms
  let hexMap =
        Map.fromList
          [ (hashHex h, hashHex h')
          | (h, h') <- Map.toList typeMap ++ Map.toList (Map.map fst terms)
          , h /= h'
          ]
      fixWord w = case T.splitOn "." w of
        (hex : rest) | Just new <- Map.lookup hex hexMap -> T.intercalate "." (new : rest)
        _ -> w
      logFile = d </> "names.log"
  present <- doesFileExist logFile
  when (present && not (Map.null hexMap)) $ do
    ls <- T.lines <$> TIO.readFile logFile
    TIO.writeFile
      (logFile <> ".retire")
      (T.unlines (map (T.unwords . map fixWord . T.words) ls))
    renameFile (logFile <> ".retire") logFile
 where
  -- Write what moved under its new hash, then remove the old file unless
  -- some other entry's new hash is that name.
  rewrite :: FilePath -> (a -> BS.ByteString) -> Map Hash (Hash, a) -> IO ()
  rewrite sub encode moved = do
    let new = Set.fromList (map fst (Map.elems moved))
    forM_ (Map.toList moved) $ \(h, (h', x)) ->
      when (h' /= h) $ do
        BS.writeFile (d </> sub </> T.unpack (hashHex h')) (encode x)
        unless (Set.member h new) $ removeFile (d </> sub </> T.unpack (hashHex h))
  typeHashes = \case
    TData h as -> Set.insert h (foldMap argHashes as)
    TFun a b -> typeHashes a <> typeHashes b
    _ -> Set.empty
  argHashes = \case
    AType t -> typeHashes t
    _ -> Set.empty

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
seedStore = seedStoreWith [] [] id

{- | 'seedStore' with log lines to put before the seed's and after them, and
a change to make to the log already there.
-}
seedStoreWith ::
  [Text] -> [Text] -> (Text -> Text) -> Store -> Codebase -> IO ()
seedStoreWith before after edit store seed = do
  writeContent store emptyCodebase seed
  let logFile = store.dir </> "names.log"
  present <- doesFileExist logFile
  old <- if present then TIO.readFile logFile else pure ""
  let tmp = store.dir </> "names.log.seed"
  TIO.writeFile
    tmp
    ( T.unlines (before ++ logEntries seedStamp emptyCodebase seed ++ after)
        <> edit old
    )
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
    -- Units and scales are names (design §3.2.12). A format-1 log flagged a
    -- reference; every name then bound to it is flagged.
    [_, "unit", target] -> (flagNames markUnit target cb, notes)
    [_, "scale", target] -> (flagNames markScale target cb, notes)
    -- A `let` that rebinds a unit or scale name makes it a plain quantity (design §3.2.12).
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
      scales =
        [ stamp <> " scale " <> n | n <- Set.toList (Set.difference new.scales old.scales)
        ]
      -- A flag a name lost while it stays bound; an unnamed label needs no line.
      unflags =
        [ stamp <> " unflag " <> n
        | n <-
            Set.toList
              ( Set.union
                  (Set.difference old.units new.units)
                  (Set.difference old.scales new.scales)
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
        ++ scales
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
    (typeVariable rootScope cb)
    (\h -> maybe (showHash h) ("." <>) (typeNameOf h cb))

{- | A signature line read back: the type parsed and converted at the root,
for a name that is bound and whose definition it holds of.
-}
replaySignature :: Text -> Text -> Codebase -> Either Text Codebase
replaySignature name text cb = do
  t <- parseType text
  sig <- either (Left . renderResolveError) Right (queryScheme rootScope cb t)
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
missing; the source must already be a store and is only read, apart from a
migration to the current format on open, which the notes mention.
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
              sourceWas <- formatOf source
              openedSource <- openStore seed source
              targetWas <- formatOf target
              openedTarget <-
                either (pure . Left) (const (openStore seed target)) openedSource
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
