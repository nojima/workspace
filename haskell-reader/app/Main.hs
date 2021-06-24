module Main where

import MyConfig

makeName :: String -> Config String
makeName baseName = do
    config <- getConfig
    pure $ prefix config ++ "-" ++ baseName

wrap :: String -> Config String
wrap name = do
    config <- getConfig
    pure $ openBracket config ++ name ++ closeBracket config

myConfig :: ConfigData
myConfig = ConfigData
    { prefix = "foobar"
    , openBracket  = "<<"
    , closeBracket = ">>"
    }

run :: Config String
run = makeName "hoge" >>= wrap

main :: IO ()
main = do
    let ret = runConfig run myConfig
    putStrLn ret
