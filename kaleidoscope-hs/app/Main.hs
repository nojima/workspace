module Main where

import Control.Monad.Trans ( MonadIO(liftIO) )
import Data.ByteString.UTF8 (ByteString)
import Data.ByteString.UTF8 qualified as ByteString
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Console.Haskeline qualified as Haskeline

import AST.Parse qualified as Parse

process :: ByteString -> IO ()
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
          let inputBS = ByteString.fromString input
          liftIO (process inputBS)
          loop
  in
  Haskeline.runInputT Haskeline.defaultSettings loop
