module Main (main) where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Data.IORef
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Eval.Driver
import Eval.Store
import System.Console.Haskeline
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO

{- | @eval@ alone starts a REPL when stdin is a terminal, otherwise reads a
program from stdin. @eval 'expr'@ evaluates one input. @eval -f file@
runs a file. @eval -i@ runs the REPL loop on stdin line by line even when
it is not a terminal, so sessions can be scripted and tested.

Every mode works against a codebase on disk (design §7.4): @--codebase DIR@
names it, otherwise a @.eval@ directory above the working directory, else
the user store. @--no-codebase@ runs in memory only.
-}
main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stdin utf8
  args <- getArgs
  let (opts, rest) = options args
  case rest of
    ["-f", path] -> TIO.readFile path >>= runOnce opts
    ["-i"] -> repl opts False
    [src] -> runOnce opts (T.pack src)
    [] -> do
      interactive <- hIsTerminalDevice stdin
      if interactive then repl opts True else TIO.getContents >>= runOnce opts
    _ -> do
      hPutStrLn
        stderr
        "usage: eval [--codebase DIR | --no-codebase] ['expr' | -f file | -i]"
      exitFailure

data Options = Options {storeDir :: Maybe FilePath, inMemory :: Bool}

options :: [String] -> (Options, [String])
options args =
  let (flags, rest) = go args
   in (flags, rest)
 where
  go = \case
    "--codebase" : d : more -> let (o, r) = go more in (o{storeDir = Just d}, r)
    "--no-codebase" : more -> let (o, r) = go more in (o{inMemory = True}, r)
    a : more -> let (o, r) = go more in (o, a : r)
    [] -> (Options Nothing False, [])

-- | A session: the prelude, then the store on top of it.
data Live = Live {session :: Session, store :: Maybe Store}

startSession :: Options -> IO Live
startSession opts = do
  base <- case preludeSession of
    Left err ->
      TIO.hPutStrLn stderr ("internal error: the prelude does not load:\n" <> err)
        >> exitFailure
    Right s -> pure s
  if opts.inMemory
    then pure (Live base Nothing)
    else do
      d <- locateStore opts.storeDir
      opened <- openStore d
      case opened of
        Left err -> TIO.hPutStrLn stderr err >> exitFailure
        Right st -> do
          (cb, notes) <- loadStore st base.codebase
          mapM_ (TIO.hPutStrLn stderr . ("note: " <>)) notes
          session <-
            either
              (\err -> TIO.hPutStrLn stderr err >> exitFailure)
              pure
              (refreshPreferences base{codebase = cb, staging = cb})
          pure (Live session (Just st))

-- | Run one input and persist whatever it changed.
step :: Live -> Text -> IO (Either Text (Live, [Text]))
step live src = case feed live.session src of
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
    Right (_, outs) -> mapM_ TIO.putStrLn outs

{- | The REPL. With a terminal, haskeline gives line editing and a history
file kept beside the codebase; scripted, lines are read plainly.
-}
repl :: Options -> Bool -> IO ()
repl opts interactive = do
  hSetBuffering stdout NoBuffering
  live0 <- startSession opts
  ref <- newIORef live0
  let historyFile = (\st -> st.dir </> "history") <$> live0.store
      settings =
        defaultSettings
          { historyFile = if interactive then historyFile else Nothing
          , autoAddHistory = interactive
          }
      behaviour = if interactive then defaultBehavior else useFileHandle stdin
  runInputTBehavior behaviour settings (loop ref)
 where
  loop :: IORef Live -> InputT IO ()
  loop ref = do
    line <- getInputLine (if interactive then "> " else "")
    case line of
      Nothing -> pure ()
      Just raw -> do
        let input = T.strip (T.pack raw)
        unless interactive (outputStrLn ("> " <> T.unpack input))
        case T.words input of
          [cmd] | cmd `elem` [":quit", ":q"] -> pure ()
          [] -> loop ref
          [":store"] -> do
            live <- liftIO (readIORef ref)
            outputStrLn (maybe "no codebase: running in memory" (.dir) live.store)
            loop ref
          -- Multi-line definitions come from a file: the layout rule treats
          -- later lines as continuations, and a REPL line is one input.
          [":load", path] -> do
            src <- liftIO (TIO.readFile (T.unpack path))
            run ref src
          _ -> run ref input
  run ref src = do
    live <- liftIO (readIORef ref)
    result <- liftIO (step live src)
    case result of
      Left err -> outputStrLn (T.unpack err)
      Right (live', outs) -> do
        liftIO (writeIORef ref live')
        mapM_ (outputStrLn . T.unpack) outs
    loop ref
