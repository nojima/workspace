module Main where

import Control.Exception
import Control.Monad.Cont
import System.IO

newMyResource :: ContT k IO Handle
newMyResource =
    ContT withMyResource
  where
    withMyResource =
        bracket
            (do
                putStrLn "Open MyResource"
                openFile "README.md" ReadMode)
            (\handle -> do
                putStrLn "Close MyResource"
                hClose handle)

main :: IO ()
main =
    (`runContT` return) $ do
        handle <- newMyResource
        contents <- liftIO $ hGetContents handle
        liftIO $ putStr contents
