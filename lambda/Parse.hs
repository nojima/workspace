{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Parse() where

import Prelude hiding (map)
import Data.Char(isSpace)
import qualified Syntax
import qualified Data.Maybe as Maybe
import Data.Function((&))
import qualified Data.ByteString.Char8 as B

type Parser a
    = B.ByteString -> Maybe (a, B.ByteString)

loc :: Syntax.Location
loc = Syntax.Location 0

string :: B.ByteString -> Parser ()
string str =
    \input ->
        case B.stripPrefix str input of
            Nothing        -> Nothing
            Just remainder -> Just ((), remainder)

oneOf :: [Parser a] -> Parser a
oneOf parsers =
    \input ->
        parsers
        & Maybe.mapMaybe ($ input)
        & Maybe.listToMaybe

bind :: Parser a -> (a -> Parser b) -> Parser b
bind parser f =
    \input ->
        case parser input of
            Nothing -> Nothing
            Just (a, remainder) ->
                (f a) remainder

map :: (a -> b) -> Parser a -> Parser b
map f parser =
    \input ->
        case parser input of
            Nothing -> Nothing
            Just (a, remainder) ->
                Just (f a, remainder)

unit :: a -> Parser a
unit a =
    \input -> Just (a, input)

whitespace :: Parser ()
whitespace =
    \input ->
        let
            (spaces, remainder) = B.span isSpace input
        in
        if B.null spaces then Nothing else Just ((), remainder)

term :: Parser Syntax.Term
term =
    oneOf
        [ literalTrue
        , literalFalse
        , if_
        ]

literalTrue :: Parser Syntax.Term
literalTrue =
    map (const $ Syntax.True_ loc) (string "true")

literalFalse :: Parser Syntax.Term
literalFalse =
    map (const $ Syntax.False_ loc) (string "false")

if_ :: Parser Syntax.Term
if_ =
    string "if"     `bind` \_ ->
    whitespace      `bind` \_ ->
    term            `bind` \condTerm ->
    whitespace      `bind` \_ ->
    string "then"   `bind` \_ ->
    whitespace      `bind` \_ ->
    term            `bind` \thenTerm ->
    whitespace      `bind` \_ ->
    string "else"   `bind` \_ ->
    whitespace      `bind` \_ ->
    term            `bind` \elseTerm ->
    unit (Syntax.If loc condTerm thenTerm elseTerm)
