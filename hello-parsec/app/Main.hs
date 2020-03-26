{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib

import Text.Megaparsec((<|>))
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Text.Megaparsec.Debug
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Void(Void)
import qualified Control.Monad as Monad

type Parser = Parsec.Parsec Void Text

data Expr
    = IntegerLiteral Integer
    | TrueLiteral
    | FalseLiteral
    | IfExpr Expr Expr Expr
    deriving (Show, Eq)

consumeSpace :: Parser ()
consumeSpace =
    Lexer.space
        Char.space1
        (Lexer.skipLineComment "//")
        (Lexer.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme consumeSpace

symbol :: Text -> Parser Text
symbol = Lexer.symbol consumeSpace

keyword :: Text -> Parser ()
keyword kwd = dbg (T.unpack kwd) $
    lexeme $ do
        Monad.void (Char.string kwd)
        Monad.void (Parsec.notFollowedBy Char.alphaNumChar)

keywordIf :: Parser ()
keywordIf = keyword "if"

keywordThen :: Parser ()
keywordThen = keyword "then"

keywordElse :: Parser ()
keywordElse = keyword "else"

keywordIsZero :: Parser ()
keywordIsZero = keyword "iszero"

integerLiteral :: Parser Expr
integerLiteral = dbg "integerLiteral" $
    IntegerLiteral <$> lexeme Lexer.decimal

trueLiteral :: Parser Expr
trueLiteral = dbg "trueLiteral" $
    TrueLiteral <$ keyword "true"

falseLiteral :: Parser Expr
falseLiteral = dbg "falseLiteral" $
    FalseLiteral <$ keyword "false"

ifExpr :: Parser Expr
ifExpr =
    IfExpr
        <$  keywordIf
        <*> expr
        <*  keywordThen
        <*> expr
        <*  keywordElse
        <*> expr

expr :: Parser Expr
expr =
    Parsec.choice
        [ integerLiteral
        , trueLiteral
        , falseLiteral
        , ifExpr
        ]

main :: IO ()
main = do
    input <- TIO.getContents
    Parsec.parseTest expr input
