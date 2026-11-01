-- | Command names and usage shared by completion and help; execution belongs to the driver and terminal.
module Metron.Command (
  Command (..),
  commandDescriptions,
  commands,
  commandHelp,
) where

import Data.Text (Text)
import Data.Text qualified as T (intercalate, null, unpack)

data Command = Command {name :: Text, arguments :: Text}

commandDescriptions :: [Command]
commandDescriptions =
  [ Command "add" ""
  , Command "update" "[--no-upgrade]"
  , Command "upgrade" "name"
  , Command "todo" ""
  , Command "scratch" ""
  , Command "forget" "name"
  , Command "edit" "[name|namespace]"
  , Command "type" "expr"
  , Command "ls" "[glob|namespace] [--all|--units|--charts|--types] [: type]"
  , Command "view" "name"
  , Command "core" "name"
  , Command "lint" "expr"
  , Command "hash" "name"
  , Command "names" "#hash"
  , Command "history" "name"
  , Command "dependents" "name"
  , Command "alias" "new old"
  , Command "unname" "name"
  , Command "rename" "old new"
  , Command "move" "name… namespace"
  , Command "namespace" "[path|.]"
  , Command "uses" ""
  , Command "use" "path [as alias]"
  , Command "unuse" "path"
  , Command "export" "[namespace] [file]"
  , Command "stdlib" "upgrade"
  , Command "exact" "expr"
  , Command "budget" "expr"
  , Command "covariance" "expr"
  , Command "backend" "[affine | double]"
  , Command
      "set"
      "[precision n | sigma k | nonlinear percent | unicode on|off | samples n | seed n | rounding nearest|random | cores k | memory|steps|depth|digits|components|outcomes n | time s|off]"
  , Command "prefer" "[unit]"
  , Command "unprefer" "unit"
  , Command "load" "file"
  , Command "quit" ""
  , Command "store" ""
  , Command "colour" "on|off"
  ]

commands :: [String]
commands = [":" ++ T.unpack c.name | c <- commandDescriptions]

commandHelp :: Text
commandHelp =
  "commands:\n"
    <> T.intercalate
      "\n"
      ["  :" <> c.name <> suffix c.arguments | c <- commandDescriptions]
 where
  suffix args = if T.null args then "" else " " <> args
