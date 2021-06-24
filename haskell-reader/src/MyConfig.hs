{-# LANGUAGE InstanceSigs, StrictData #-}
module MyConfig
    ( ConfigData(..)
    , Config
    , getConfig
    , runConfig
    ) where

data ConfigData = ConfigData
    { prefix :: String
    , openBracket :: String
    , closeBracket :: String
    }
    deriving (Show)

newtype Config a = Config (ConfigData -> a)

instance Functor Config where
    fmap :: (a -> b) -> Config a -> Config b
    fmap f (Config g) =
        Config (f . g)

instance Applicative Config where
    pure :: a -> Config a
    pure x =
        Config (const x)

    (<*>) :: Config (a -> b) -> Config a -> Config b
    (<*>) (Config f) (Config g) =
        Config $ \config ->
            let
                f' = f config
                x  = g config
            in
                f' x

instance Monad Config where
    (>>=) :: Config a -> (a -> Config b) -> Config b
    (>>=) (Config f) g =
        Config $ \config ->
            let
                x        = f config
                Config y = g x
            in
                y config

getConfig :: Config ConfigData
getConfig =
    Config id

runConfig :: Config a -> ConfigData -> a
runConfig (Config f) config =
    f config
