{-# LANGUAGE OverloadedStrings #-}
module Calc.Parse
    ( ParseError(..)
    , parse
    ) where

import Calc.Expr (Expr)
import qualified Calc.Expr as Expr

import qualified Control.Monad.Combinators.Expr as Expr
import Data.Text as T
import Data.Void
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import qualified Text.Megaparsec.Error as Erro

type Parser = Parsec.Parsec Void T.Text

--------------------------------------------------------------------------------

space :: Parser ()
space =
    Lexer.space
        Char.space1
        (Lexer.skipLineComment "--")
        (Lexer.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme =
    Lexer.lexeme space

symbol :: Text -> Parser ()
symbol s =
    () <$ Lexer.symbol space s

decimal :: Parser Integer
decimal =
    lexeme Lexer.decimal

--------------------------------------------------------------------------------

intLiteral :: Parser Expr
intLiteral =
    Expr.IntLiteral <$> decimal

parens :: Parser Expr
parens =
    Parsec.between
        (symbol "(")
        (symbol ")")
        expr

term :: Parser Expr
term =
    Parsec.choice
        [ intLiteral
        , parens
        ]

expr :: Parser Expr
expr =
    Expr.makeExprParser
        term
        [ [ binaryOperator Expr.InfixL "*" Expr.Mul
          , binaryOperator Expr.InfixL "/" Expr.Div
          ]
        , [ binaryOperator Expr.InfixL "+" Expr.Add
          , binaryOperator Expr.InfixL "-" Expr.Sub
          ]
        ]
        <?> "expression"
  where
    binaryOperator infix_ name op =
        infix_ $ Parsec.label "binary operator" $
            Expr.BinOp
                <$> pure op
                <*  symbol name

program :: Parser Expr
program =
    space *> expr <* Parsec.eof

--------------------------------------------------------------------------------

newtype ParseError = ParseError Text
    deriving (Show, Eq)

parse :: Text -> Either ParseError Expr
parse source =
    case Parsec.parse program "" source of
        Left errors ->
            let message = Parsec.errorBundlePretty errors in
            Left (ParseError (T.pack message))
        Right result ->
            Right result
