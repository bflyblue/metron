module Main (main) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.IORef
import Data.List (find)
import Data.Maybe (catMaybes, isNothing, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Metron.Codebase (emptyCodebase)
import Metron.Driver
import Metron.Repl qualified as R
import Metron.Store
import System.Console.Haskeline
import System.Directory (getTemporaryDirectory, removeFile)
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath ((</>))
import System.IO
import System.Process (createProcess, delegate_ctlc, proc, waitForProcess)

{- | @metron@ alone starts a REPL when stdin is a terminal, otherwise reads a
program from stdin. @metron 'expr'@ evaluates one input. @metron -f file@
runs a file. @metron -i@ runs the REPL loop on stdin line by line even when
it is not a terminal, so sessions can be scripted and tested.

Every mode works against a codebase on disk (design §7.4): @--codebase DIR@
names it, otherwise a @.metron@ directory above the working directory, else
the user store. @--no-codebase@ runs in memory only. @--merge OTHER@ merges
the store at OTHER into that codebase and exits.
-}
main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stdin utf8
  args <- getArgs
  let (opts, rest) = options args
  case rest of
    _
      | Just other <- opts.mergeFrom ->
          if null rest && not opts.inMemory then merge opts other else usage
    ["-f", path] -> TIO.readFile path >>= runOnce opts
    ["-i"] -> repl opts False
    [src] -> runOnce opts (T.pack src)
    [] -> do
      interactive <- hIsTerminalDevice stdin
      if interactive then repl opts True else TIO.getContents >>= runOnce opts
    _ -> usage
 where
  usage = do
    hPutStrLn
      stderr
      "usage: metron [--codebase DIR | --no-codebase] ['expr' | -f file | -i]\n\
      \       metron [--codebase DIR] --merge OTHER"
    exitFailure

data Options = Options
  { storeDir :: Maybe FilePath
  , inMemory :: Bool
  , mergeFrom :: Maybe FilePath
  }

options :: [String] -> (Options, [String])
options args =
  let (flags, rest) = go args
   in (flags, rest)
 where
  go = \case
    "--codebase" : d : more -> let (o, r) = go more in (o{storeDir = Just d}, r)
    "--no-codebase" : more -> let (o, r) = go more in (o{inMemory = True}, r)
    "--merge" : d : more -> let (o, r) = go more in (o{mergeFrom = Just d}, r)
    a : more -> let (o, r) = go more in (o, a : r)
    [] -> (Options Nothing False Nothing, [])

{- | Merge the store at OTHER into this codebase (design §7.4) and say what
came across. OTHER is only read, and a store of an older format is
refused.
-}
merge :: Options -> FilePath -> IO ()
merge opts other = do
  d <- locateStore opts.storeDir
  result <- mergeStores stdlibSeed d other
  case result of
    Left err -> TIO.hPutStrLn stderr err >> exitFailure
    Right report -> do
      TIO.putStrLn ("merged " <> T.pack other <> " into " <> T.pack d)
      TIO.putStrLn ("terms copied: " <> tshow report.termsCopied)
      TIO.putStrLn ("types copied: " <> tshow report.typesCopied)
      TIO.putStrLn ("log lines added: " <> tshow report.linesAdded)
      mapM_ (TIO.putStrLn . ("note: " <>)) report.notes
 where
  tshow = T.pack . show

-- | A session and the store it persists to, if any.
data Live = Live {session :: Session, store :: Maybe Store}

{- | The session to start with (design §7.7): in memory, a seeded one; else
the store, created and seeded if it does not exist yet, loaded on top of
the empty codebase.
-}
startSession :: Options -> IO Live
startSession opts =
  if opts.inMemory
    then (`Live` Nothing) <$> orFail seededSession
    else do
      d <- locateStore opts.storeDir
      opened <- openStore stdlibSeed d
      case opened of
        Left err -> TIO.hPutStrLn stderr err >> exitFailure
        Right st -> do
          (cb, notes) <- loadStore st emptyCodebase
          mapM_ (TIO.hPutStrLn stderr . ("note: " <>)) notes
          session <-
            either
              (\err -> TIO.hPutStrLn stderr err >> exitFailure)
              pure
              (refreshPreferences emptySession{codebase = cb, staging = cb})
          pure (Live session (Just st))

-- | The library is part of the build; if it does not load, nothing can start.
orFail :: Either Text a -> IO a
orFail =
  either
    ( \err ->
        TIO.hPutStrLn
          stderr
          ("internal error: the standard library does not load:\n" <> err)
          >> exitFailure
    )
    pure

-- | Run one input and persist whatever it changed.
step :: Live -> Text -> IO (Either Text (Live, [Text]))
step = stepWith feed

{- | 'step' with a chosen way to feed: a file read by @:load@ keeps its
@use@s to itself (design §7.6).
-}
stepWith ::
  (Session -> Text -> Either Text (Session, [Text])) ->
  Live ->
  Text ->
  IO (Either Text (Live, [Text]))
stepWith feeder live src = case feeder live.session src of
  Left err -> pure (Left err)
  Right (session', outs) -> do
    mapM_ (\st -> sync st live.session.codebase session'.codebase) live.store
    pure (Right (live{session = session'}, outs))

runOnce :: Options -> Text -> IO ()
runOnce opts src = do
  live <- startSession opts
  result <- step live src
  case result of
    Left err -> TIO.hPutStrLn stderr err >> exitFailure
    Right (_, outs) -> do
      mapM_ TIO.putStrLn outs
      -- One input opens no editor (design §7.3); the note goes to stderr so
      -- the source stays pasteable.
      when (listToMaybe (T.words src) == Just ":edit")
        $ TIO.hPutStrLn stderr (editorNote "one input opens no editor")

{- | The REPL. With a terminal, haskeline gives line editing, completion
(design §7.3) and a history file kept beside the codebase; scripted, lines
are read plainly. An input goes on at a continuation line while
'R.needsMore' says so, in both modes. Output is coloured when stdout is a
terminal, @TERM@ is not @dumb@ and @NO_COLOR@ is unset, or as
@:colour on|off@ says.
-}
repl :: Options -> Bool -> IO ()
repl opts interactive = do
  hSetBuffering stdout NoBuffering
  live0 <- startSession opts
  ref <- newIORef live0
  colourRef <- newIORef =<< colourByDefault
  let historyFile = (\st -> st.dir </> "history") <$> live0.store
      settings =
        setComplete
          (completer ref)
          defaultSettings
            { historyFile = if interactive then historyFile else Nothing
            , autoAddHistory = interactive
            }
      behaviour = if interactive then defaultBehavior else useFileHandle stdin
  runInputTBehavior behaviour settings (loop ref colourRef)
 where
  loop :: IORef Live -> IORef Bool -> InputT IO ()
  loop ref colourRef = do
    colour <- liftIO (readIORef colourRef)
    line <- getInputLine (if interactive then prompt colour "> " else "")
    case line of
      Nothing -> pure ()
      Just raw -> do
        let first = T.strip (T.pack raw)
        echoAt "> " first
        whole <- more colour first
        case whole of
          Nothing -> do
            emit ref colour (Right ["(input abandoned)"])
            again
          Just input -> dispatch colour input
   where
    -- Scripted, each line is echoed after the prompt it was read at,
    -- highlighted as the REPL would show it.
    echoAt p l = unless interactive $ do
      colour <- liftIO (readIORef colourRef)
      live <- liftIO (readIORef ref)
      outputStrLn (T.unpack (R.echoInputAt p colour (R.namesOf live.session) l))
    -- Continuation lines (design §7.3): read on at the "… " prompt while
    -- the input so far needs more. A continuation line keeps its
    -- indentation, which layout reads. Ctrl-C or end of input abandons it.
    more colour input
      | R.needsMore input = do
          next <-
            handleInterrupt
              (pure Nothing)
              (withInterrupt (getInputLine (if interactive then prompt colour "… " else "")))
          case next of
            Nothing -> pure Nothing
            Just raw -> do
              let l = T.stripEnd (T.pack raw)
              echoAt "… " l
              more colour (input <> "\n" <> l)
      | otherwise = pure (Just (T.stripEnd input))
    dispatch colour input = case T.words input of
      [cmd] | cmd `elem` [":quit", ":q"] -> pure ()
      [] -> again
      [":store"] -> do
        live <- liftIO (readIORef ref)
        outputStrLn (maybe "no codebase: running in memory" (.dir) live.store)
        again
      -- A REPL-level setting: the Driver never sees it.
      cmd : args | cmd `elem` [":colour", ":color"] -> do
        case args of
          [] -> outputStrLn ("colour " <> if colour then "on" else "off")
          ["on"] -> liftIO (writeIORef colourRef True)
          ["off"] -> liftIO (writeIORef colourRef False)
          _ -> emit ref colour (Left "usage: :colour [on|off]")
        again
      -- A file is one input too, its later lines continuations by layout.
      [":load", path] -> do
        src <- liftIO (TIO.readFile (T.unpack path))
        run feedFile src
      -- The codebase as source, into a file (design §7.4); without a file
      -- the Driver prints it.
      ":export" : args -> do
        live <- liftIO (readIORef ref)
        case exportRequest live.session args of
          Right (Just file, source) -> do
            liftIO (TIO.writeFile file (if T.null source then source else source <> "\n"))
            emit
              ref
              colour
              ( Right
                  ( ("exported to " <> T.pack file)
                      : [ "note: the pending scratch is not exported; :add or :update it first"
                        | not (null live.session.scratch)
                        ]
                  )
              )
            again
          _ -> run feed input
      -- The editor round trip (design §7.3): the scope to a file, the
      -- editor, and the file reconciled with the codebase. Scripted, or
      -- with no editor, the source it would open is printed instead.
      ":edit" : args -> do
        live <- liftIO (readIORef ref)
        editor <- liftIO editorCommand
        case editRequest live.session args of
          Left err -> emit ref colour (Left err)
          Right (EditResume target path) -> do
            text <- liftIO (try (readUtf8 path))
            case text of
              Left (e :: SomeException) ->
                emit
                  ref
                  colour
                  (Left ("cannot read " <> T.pack path <> ": " <> T.pack (displayException e)))
              Right src -> reconcile colour target path False src
          Right (EditOpen target file paste) -> case (editor, file) of
            _ | not interactive -> fallback colour paste "scripted input opens no editor"
            (Nothing, _) -> fallback colour paste "no editor: set VISUAL or EDITOR to edit in place"
            (_, Left err) -> emit ref colour (Left err)
            (Just ed, Right text) -> do
              path <- liftIO (writeTemp text)
              status <- liftIO (runEditor ed path)
              after <- liftIO (try (readUtf8 path))
              case (status, after) of
                (Left why, _) -> done path ("nothing to do: the editor did not run (" <> why <> ")")
                (Right (ExitFailure k), _) ->
                  done
                    path
                    ("nothing to do: the editor exited with status " <> T.pack (show k))
                (_, Left (e :: SomeException)) ->
                  emit
                    ref
                    colour
                    (Left ("cannot read " <> T.pack path <> ": " <> T.pack (displayException e)))
                (Right ExitSuccess, Right src)
                  | src == text -> done path "nothing to do: the file was not changed"
                  | otherwise -> reconcile colour target path True src
        again
      _ -> run feed input
    again = loop ref colourRef
    fallback colour paste why = emit ref colour (Right (paste ++ [editorNote why]))
    -- Nothing to do: the temporary file goes.
    done path msg = do
      liftIO (removeQuietly path)
      colour <- liftIO (readIORef colourRef)
      emit ref colour (Right [msg])
    -- Reconcile the file and persist the result; on an error the file is
    -- kept, with the command that resumes from it.
    reconcile colour target path temporary src = do
      live <- liftIO (readIORef ref)
      result <- liftIO (stepWith (\s _ -> applyEdit target src s) live "")
      case result of
        Left err -> do
          emit ref colour (Left err)
          emit
            ref
            colour
            ( Right
                [ "note: the file is kept at "
                    <> T.pack path
                    <> "; fix it, then :edit --file "
                    <> T.pack path
                    <> editScopeArgs live.session target
                ]
            )
        Right (live', outs) -> do
          liftIO (writeIORef ref live')
          when temporary (liftIO (removeQuietly path))
          emit ref colour (Right outs)
    run feeder src = do
      live <- liftIO (readIORef ref)
      result <- liftIO (stepWith feeder live src)
      colour <- liftIO (readIORef colourRef)
      case result of
        Left err -> emit ref colour (Left err)
        Right (live', outs) -> do
          liftIO (writeIORef ref live')
          emit ref colour (Right outs)
      again

-- | The editor @:edit@ opens: @VISUAL@, else @EDITOR@, when set and not empty.
editorCommand :: IO (Maybe String)
editorCommand = do
  visual <- lookupEnv "VISUAL"
  editor <- lookupEnv "EDITOR"
  pure (find (not . all isSpace) (catMaybes [visual, editor]))

-- | Write the file @:edit@ opens to a new temporary file, @metron-edit-….metron@.
writeTemp :: Text -> IO FilePath
writeTemp text = do
  dir <- getTemporaryDirectory
  (path, h) <- openTempFile dir "metron-edit-.metron"
  hSetEncoding h utf8
  TIO.hPutStr h text
  hClose h
  pure path

readUtf8 :: FilePath -> IO Text
readUtf8 path = withFile path ReadMode $ \h -> hSetEncoding h utf8 >> TIO.hGetContents h

removeQuietly :: FilePath -> IO ()
removeQuietly path = either (\(_ :: SomeException) -> ()) id <$> try (removeFile path)

{- | Run the editor on a file and wait for it, with the terminal handed over:
the editor's own handles are the REPL's, and Ctrl-C goes to it. The
command goes through the shell, so @EDITOR="emacs -nw"@ works. haskeline
holds the terminal only while it reads a line, so it needs no suspending.
-}
runEditor :: String -> FilePath -> IO (Either Text ExitCode)
runEditor ed path = do
  result <- try $ do
    (_, _, _, ph) <-
      createProcess
        (proc "sh" ["-c", ed <> " \"$1\"", "sh", path]){delegate_ctlc = True}
    waitForProcess ph
  pure
    ( either
        (\(e :: SomeException) -> Left (T.pack (displayException e)))
        Right
        result
    )

{- | Print what 'step' returned: as is without colour, painted line by line
with it (design §7.3), by the names of the session as it now is.
-}
emit :: IORef Live -> Bool -> Either Text [Text] -> InputT IO ()
emit ref colour result = do
  live <- liftIO (readIORef ref)
  mapM_ (outputStrLn . T.unpack) (R.render colour (R.namesOf live.session) result)

{- | A prompt, bold with colour. haskeline treats @\\SOH…\\STX@ as zero
width and strips the markers, so the cursor lands where it should.
-}
prompt :: Bool -> String -> String
prompt colour p
  | colour = "\SOH\ESC[1m\STX" <> p <> "\SOH\ESC[0m\STX"
  | otherwise = p

-- | Colour by default when stdout is a terminal that can show it.
colourByDefault :: IO Bool
colourByDefault = do
  terminal <- hIsTerminalDevice stdout
  term <- lookupEnv "TERM"
  noColour <- lookupEnv "NO_COLOR"
  pure (terminal && term /= Just "dumb" && isNothing noColour)

{- | Tab completion (design §7.3) against the session as it is when TAB is
pressed; file names after @:load@.
-}
completer :: IORef Live -> CompletionFunc IO
completer ref input = do
  live <- readIORef ref
  case R.complete live.session input of
    Nothing -> completeFilename input
    Just (prev, cs) ->
      pure (prev, [Completion c.replacement c.display c.isFinished | c <- cs])
