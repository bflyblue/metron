module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Eval.Driver
import Eval.Eval (defaultConfig)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO

-- | @eval@ alone starts a REPL when stdin is a terminal, otherwise reads a
-- program from stdin. @eval 'expr'@ evaluates one input. @eval -f file@
-- runs a file. @eval -i@ runs the REPL loop on stdin line by line even when
-- it is not a terminal, so sessions can be scripted and tested.
main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stdin utf8
  args <- getArgs
  case args of
    ["-f", path] -> TIO.readFile path >>= runOnce
    ["-i"] -> repl
    [src] -> runOnce (T.pack src)
    [] -> do
      interactive <- hIsTerminalDevice stdin
      if interactive then repl else TIO.getContents >>= runOnce
    _ -> do
      hPutStrLn stderr "usage: eval ['expr' | -f file | -i]"
      exitFailure

runOnce :: Text -> IO ()
runOnce src = case feed defaultConfig emptySession src of
  Left err -> TIO.hPutStrLn stderr err >> exitFailure
  Right (_, outs) -> mapM_ TIO.putStrLn outs

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  loop emptySession
  where
    loop session = do
      putStr "> "
      eof <- isEOF
      unless eof $ do
        line <- TIO.getLine
        case T.words (T.strip line) of
          [cmd] | cmd `elem` [":quit", ":q"] -> pure ()
          [] -> loop session
          -- Multi-line definitions come from a file: the layout rule treats
          -- later lines as continuations, and a REPL line is one input.
          [":load", path] -> do
            src <- TIO.readFile (T.unpack path)
            run session src
          _ -> run session line
    run session src = case feed defaultConfig session src of
      Left err -> TIO.putStrLn err >> loop session
      Right (session', outs) -> mapM_ TIO.putStrLn outs >> loop session'
