{-# LANGUAGE OverloadedStrings #-}
module Calc.Expr
    ( Expr(..)
    , Operator(..)
    )
    where

import Calc.Pretty
import qualified Data.Text as T

data Expr
    = IntLiteral !Integer
    | BinOp !Operator !Expr !Expr
    deriving (Show, Eq)

data Operator
    = Add
    | Sub
    | Mul
    | Div
    deriving (Show, Eq)

instance Pretty Expr where
    pretty expr =
        case expr of
            IntLiteral i ->
                pretty i

            BinOp op lhs rhs ->
                "("
                <> pretty op
                <> " "
                <> pretty lhs
                <> " "
                <> pretty rhs
                <> ")"

instance Pretty Operator where
    pretty op =
        case op of
            Add -> "+"
            Sub -> "-"
            Mul -> "*"
            Div -> "/"
