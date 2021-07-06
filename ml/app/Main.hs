module Main where

import qualified System.IO as IO
import qualified System.Exit as Exit
import qualified Data.Text.IO as TIO
import qualified Parse

main :: IO ()
main = do
    IO.putStr "> "
    IO.hFlush IO.stdout
    source <- TIO.getLine
    case Parse.parse source of
        Left errorMessage -> do
            IO.hPutStr IO.stderr errorMessage
        Right ast -> do
            print ast
    main
