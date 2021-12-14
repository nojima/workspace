module Main where

import Control.Monad.Trans
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Console.Haskeline qualified as Haskeline

import AST.Parse qualified as Parse

process :: Text -> IO ()
process line = do
  let res = Parse.parse line
  case res of
    Left (Parse.Error message) ->
      Text.putStrLn message
    Right expr ->
      mapM_ print expr

main :: IO ()
main =
  let
    loop = do
      input <- Haskeline.getInputLine "ready> "
      case input of
        Nothing ->
          Haskeline.outputStrLn "Goodbye."
        Just input -> do
          liftIO (process (Text.pack input))
          loop
  in
  Haskeline.runInputT Haskeline.defaultSettings loop
