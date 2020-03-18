{-# OPTIONS -Wall -Werror #-}
module Syntax
    ( Term(..)
    , Location(..)
    )
    where

data Term
    = True_ Location
    | False_ Location
    | If Location Term Term Term
    | Zero Location
    | Succ Location Term
    | Pred Location Term
    | IsZero Location Term
    deriving (Show)

data Location
    = Location Int

instance Show Location where
    show (Location line) = "L" ++ show line
