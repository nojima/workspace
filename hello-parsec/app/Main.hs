{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib

import Text.Megaparsec((<|>))
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Data.Text(Text)
import qualified Data.Text as T
import Data.Void(Void)
import qualified Control.Monad as Monad

type Parser = Parsec.Parsec Void Text

-- if iszero 0 then true else false

data Token
    = KeywordIf
    | KeywordThen
    | KeywordElse
    | KeywordIsZero
    | KeywordTrue
    | KeywordFalse
    | IntegerToken Integer
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

token :: Parser Token
token = keywordToken <|> integerToken

keywordToken :: Parser Token
keywordToken =
    Parsec.choice
        [ KeywordIf     <$ symbol "if"
        , KeywordThen   <$ symbol "then"
        , KeywordElse   <$ symbol "else"
        , KeywordIsZero <$ symbol "iszero"
        , KeywordTrue   <$ symbol "true"
        , KeywordFalse  <$ symbol "false"
        ]

integerToken :: Parser Token
integerToken =
    IntegerToken <$> lexeme Lexer.decimal

main :: IO ()
main = someFunc