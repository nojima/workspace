{-# LANGUAGE OverloadedStrings #-}
module Lib
    ( someFunc
    ) where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Debug as Debug
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Control.Monad

type Parser = Parsec Void Text

data URL = URL
    { urlScheme    :: Scheme
    , urlAuthority :: Maybe Authority
    }
    deriving (Eq, Show)

data Scheme
    = SchemeData
    | SchemeFile
    | SchemeFTP
    | SchemeHTTP
    | SchemeHTTPS
    | SchemeIRC
    | SchemeMailto
    deriving (Eq, Show)

data Authority = Authority
    { authUser :: Maybe (Text, Text) -- (user, password)
    , authHost :: Text
    , authPort :: Maybe Int
    } deriving (Eq, Show)

pScheme :: Parser Scheme
pScheme =
    choice 
        [ SchemeData   <$ string "data"
        , SchemeFile   <$ string "file"
        , SchemeFTP    <$ string "ftp"
        , SchemeHTTPS  <$ string "https"
        , SchemeHTTP   <$ string "http"
        , SchemeIRC    <$ string "irc"
        , SchemeMailto <$ string "mailto"
        ]
    <?> "valid scheme"

pAuthority :: Parser (Maybe Authority)
pAuthority = optional $ do
    void (string "//")
    authUser <- optional . try $ do
        user <- T.pack <$> some alphaNumChar <?> "username"
        void (char ':')
        password <- T.pack <$> some alphaNumChar <?> "password"
        void (char '@')
        return (user, password)
    authHost <- T.pack <$> some (alphaNumChar <|> char '.') <?> "hostname"
    authPort <- optional (char ':' *> label "port number" L.decimal)
    return Authority
        { authUser = authUser
        , authHost = authHost
        , authPort = authPort
        }

pURL :: Parser URL
pURL = do
    scheme <- pScheme
    _ <- char ':'
    authority <- pAuthority
    eof
    return (URL scheme authority)

consumeSpace :: Parser ()
consumeSpace =
    L.space
        space1
        (L.skipLineComment "//")
        (L.skipBlockComment "%s" "%s")


someFunc :: IO ()
someFunc = do
    parseTest pURL "foo"
    parseTest pURL "http:"
    parseTest pURL "https://mark:secret@example.com"
    parseTest pURL "https://mark:secret@example.com:123"
    parseTest pURL "https://example.com:123"
    parseTest pURL "https://mark@example.com:123"
    parseTest pURL "https://mark:@example.com"
