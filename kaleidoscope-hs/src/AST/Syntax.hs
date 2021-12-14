module AST.Syntax where

import Data.ByteString.Char8 (ByteString)

type Name = ByteString

data Expr
  = Float    Double
  | BinOp    BinOp Expr Expr
  | Variable Name
  | Call     Name [Expr]
  | Function Name [Expr] Expr
  | Extern   Name [Expr]
  deriving (Eq, Ord, Show)

data BinOp
  = Add
  | Sub
  | Mul
  | Div
  deriving (Eq, Ord, Show)
