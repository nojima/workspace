{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Parse() where

import Data.Char(isSpace)
import qualified Syntax
import qualified Data.Maybe as Maybe
import Data.Function((&))
import Control.Applicative(Alternative, (<|>))
import qualified Data.ByteString.Char8 as B

newtype Parser a =
    Parser { runParser :: B.ByteString -> Maybe (a, B.ByteString) }

instance Functor Parser where
    fmap f (Parser parser) =
        Parser $ \input ->
            case parser input of
                Nothing             -> Nothing
                Just (a, remainder) -> Just (f a, remainder)

instance Applicative Parser where
    pure x =
        Parser $ \input ->
            Just (x, input)

    (Parser pFunc) <*> (Parser pArg) =
        Parser $ \input -> do
            (func, remainder1) <- pFunc input
            (arg, remainder2) <- pArg remainder1
            return (func arg, remainder2)

instance Alternative Parser where
    (Parser p1) <|> (Parser p2) =
        Parser $ \input ->
            (p1 input) <|> (p2 input)

loc :: Syntax.Location
loc = Syntax.Location 0

string :: B.ByteString -> Parser ()
string str =
    Parser $ \input ->
        case B.stripPrefix str input of
            Nothing        -> Nothing
            Just remainder -> Just ((), remainder)

whitespace :: Parser ()
whitespace =
    Parser $ \input ->
        let
            (spaces, remainder) = B.span isSpace input
        in
        if B.null spaces
        then Nothing
        else Just ((), remainder)

term :: Parser Syntax.Term
term =
    literalTrue
    <|> literalFalse
    <|> if_

literalTrue :: Parser Syntax.Term
literalTrue =
    fmap (const $ Syntax.True_ loc) (string "true")

literalFalse :: Parser Syntax.Term
literalFalse =
    fmap (const $ Syntax.False_ loc) (string "false")

if_ :: Parser Syntax.Term
if_ =
    let
        f _ _ condTerm _ _ _ thenTerm _ _ _ elseTerm =
            Syntax.If loc condTerm thenTerm elseTerm
    in
    f
    <$> string "if"
    <*> whitespace
    <*> term
    <*> whitespace
    <*> string "then"
    <*> whitespace
    <*> term
    <*> whitespace
    <*> string "else"
    <*> whitespace
    <*> term
