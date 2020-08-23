module Main where

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

{-
-- 全く同期せずにカウントしていくコード (正しくカウントできない):

import Data.IORef (IORef, newIORef, readIORef, writeIORef)

incrementCounter :: IORef Int -> IO ()
incrementCounter counter = do
    n <- readIORef counter
    writeIORef counter (n + 1)

main :: IO ()
main = do
    counter <- newIORef 0

    replicateConcurrently_ 100000 $
        incrementCounter counter

    result <- readIORef counter
    print result
-}
