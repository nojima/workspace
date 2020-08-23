module Main where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM.TVar (TVar, newTVar, readTVar, writeTVar)
import Control.Concurrent.Async (replicateConcurrently_)
import Control.Monad.STM (STM, atomically)

incrementCounter :: TVar Int -> STM ()
incrementCounter counter = do
    n <- readTVar counter
    writeTVar counter (n + 1)

main :: IO ()
main = do
    counter <- atomically $ newTVar 0

    replicateConcurrently_ 100000 $
        atomically $ incrementCounter counter

    result <- atomically $ readTVar counter
    print result
