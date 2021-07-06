{-# LANGUAGE StrictData #-}
module Syntax
    ( Expr(..)
    , BinOp(..)
    ) where

import qualified Data.Text as T
import           Identifier (Identifier)
import qualified Identifier

newtype Program
    = Program Expr
    deriving (Show, Eq)

data Expr
    = Variable Identifier
    | Int      Integer
    | Bool     Bool
    | BinOp    BinOp Expr Expr
    | If       Expr Expr Expr
    deriving (Show, Eq)

data BinOp = Add | Mul | Lt
    deriving (Show, Eq)
