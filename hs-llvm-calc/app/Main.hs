{-# LANGUAGE OverloadedStrings #-}
module Main where

import Calc.Pretty
import qualified Calc.Parse as Parse

import qualified System.IO as IO
import qualified System.Exit as Exit
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
    source <- TIO.getContents

    ast <- case Parse.parse source of
        Left (Parse.ParseError message) -> do
            TIO.hPutStrLn IO.stderr ("ParseError: " <> message)
            Exit.exitFailure

        Right result ->
            return result

    TIO.putStrLn (pretty ast)
