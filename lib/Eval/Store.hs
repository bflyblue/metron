{- | The codebase on disk (design §7.4).

A store is a directory:

@
format          "eval codebase 1"
terms\/\<hex\>    one term per file, in the storage encoding ("Eval.Hash")
names.log       append-only: time, then  bind name ref | unname name | unit name | scale name | prefer text | unprefer text
@

Terms are content-addressed, so they never conflict and are only ever
added. Everything label-level (names, their history, unit declarations) is
the log replayed in order, which is also what makes two stores mergeable:
concatenate the logs and sort by time.

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
) where

import Control.Monad (foldM, foldM_, forM_, unless, when)
import Data.ByteString qualified as BS
import Data.Either (lefts)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Time.Clock.POSIX (getPOSIXTime)
import Eval.Codebase
import Eval.Core
import Eval.Hash
import Eval.Resolve (storeTerm)
import System.Directory
import System.FilePath

newtype Store = Store {dir :: FilePath}

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
  formatLine v = "eval codebase " <> tshow v
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
    let old = Map.fromList [x | Just x <- decoded]
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
  files <- listDirectory (store.dir </> "terms")
  decoded <- mapM readTerm files
  let loaded = Map.fromList [(h, t) | Right (h, t) <- decoded]
      decodeNotes = lefts decoded
  let (cb, enterNotes) = enterAll loaded base
  let logFile = store.dir </> "names.log"
  present <- doesFileExist logFile
  logLines <- if present then T.lines <$> TIO.readFile logFile else pure []
  let (cb', logNotes) = foldl replay (cb, []) (zip [1 :: Int ..] logLines)
  pure (cb', decodeNotes ++ enterNotes ++ reverse logNotes)
 where
  readTerm file = do
    raw <- BS.readFile (store.dir </> "terms" </> file)
    pure $ case hashFromHex (T.pack file) of
      Nothing -> Left ("terms/" <> T.pack file <> ": not a hash, ignored")
      Just h -> case decodeStored raw of
        Left err -> Left ("terms/" <> T.pack file <> ": " <> err <> ", ignored")
        Right t
          | hashTerm t /= h ->
              Left ("terms/" <> T.pack file <> ": content does not match its hash, ignored")
          | otherwise -> Right (h, t)

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
  let fresh = Map.keys (Map.difference new.terms old.terms)
  foldM_ writeClosure Set.empty fresh
  now <- (round <$> getPOSIXTime) :: IO Integer
  let stamp = tshow now
      binds =
        [ stamp <> " bind " <> name <> " " <> refText r
        | (name, r) <- Map.toList new.names
        , Map.lookup name old.names /= Just r
        ]
      unnames =
        [ stamp <> " unname " <> name
        | name <- Map.keys (Map.difference old.names new.names)
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
      entries = binds ++ unnames ++ units ++ scales ++ prefers ++ unprefers
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
