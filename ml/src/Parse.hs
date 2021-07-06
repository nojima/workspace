{-# LANGUAGE StrictData, OverloadedStrings #-}
module Parse (parse) where

import qualified Data.Char as Char
import qualified Data.Bifunctor as Bifunctor
import           Data.Function ((&))
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Void (Void)
import qualified Control.Applicative as Applicative
import qualified Control.Monad.Combinators.Expr as CombinatorsExpr
import           Text.Megaparsec (Parsec, (<?>))
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as ParsecChar
import qualified Text.Megaparsec.Char.Lexer as Lexer
import qualified Text.Megaparsec.Error as ParsecError
import qualified Syntax
import           Identifier (Identifier)
import qualified Identifier

type Parser a = Parsec Void Text a

---------------------------------------------------------------------------------------------------

space :: Parser ()
space =
    Lexer.space
        ParsecChar.space1
        Applicative.empty
        (Lexer.skipBlockComment "(*" "*)")

lexeme :: Parser a -> Parser a
lexeme =
    Lexer.lexeme space

symbol :: Text -> Parser ()
symbol s =
    () <$ Lexer.symbol space s

decimal :: Parser Integer
decimal =
    lexeme Lexer.decimal

keywords :: Set Text
keywords = Set.fromList ["if", "then", "else", "true", "false"]

keyword :: Text -> Parser ()
keyword str =
    lexeme $
        () <$ ParsecChar.string str
           <* Parsec.notFollowedBy ParsecChar.alphaNumChar

identifierOrKeyword :: Parser Text
identifierOrKeyword =
    let
        alphaChar =
            Parsec.satisfy
                (\c -> (Char.isAlpha c || c == '_') && Char.isAscii c)
                <?> "alphabet"

        alnumChars =
            Parsec.takeWhileP
                (Just "alphabets or numbers")
                (\c -> (Char.isAlpha c || Char.isNumber c || c == '_') && Char.isAscii c)
    in
        lexeme (T.cons <$> alphaChar <*> alnumChars)

identifier :: Parser Identifier
identifier =
    Parsec.try $ Parsec.label "identifier" $ do
        offset <- Parsec.getOffset
        word <- identifierOrKeyword
        if Set.member word keywords then
            let
                actual = ParsecError.Tokens (NonEmpty.fromList (T.unpack word))
                expected = ParsecError.Label (NonEmpty.fromList "identifier")
                err = ParsecError.TrivialError offset (Just actual) (Set.singleton expected)
            in
                Parsec.parseError err
        else
            return $ Identifier.fromText word

---------------------------------------------------------------------------------------------------

toplevel :: Parser Syntax.Expr
toplevel =
    expr <* symbol ";;"

expr :: Parser Syntax.Expr
expr =
    Parsec.choice [ ifExpr, simpleExpr ]

ifExpr :: Parser Syntax.Expr
ifExpr =
    Syntax.If
    <$  keyword "if"
    <*> expr
    <*  keyword "then"
    <*> expr
    <*  keyword "else"
    <*> expr

simpleExpr :: Parser Syntax.Expr
simpleExpr =
    CombinatorsExpr.makeExprParser
        term
        [ [ binaryOperator CombinatorsExpr.InfixL "*" Syntax.Mul ]
        , [ binaryOperator CombinatorsExpr.InfixL "+" Syntax.Add ]
        , [ binaryOperator CombinatorsExpr.InfixN "<" Syntax.Lt ]
        ]
        <?> "expression"
  where
    binaryOperator infix_ name op =
        infix_ $ Parsec.label "binary operator" $
            Syntax.BinOp op <$ symbol name

term :: Parser Syntax.Expr
term =
    Parsec.choice
        [ intLiteral
        , boolLiteral
        , variable
        , parens
        ]

boolLiteral :: Parser Syntax.Expr
boolLiteral =
    Syntax.Bool <$> Parsec.choice
        [ True  <$ keyword "true"
        , False <$ keyword "false"
        ]

intLiteral :: Parser Syntax.Expr
intLiteral =
    Syntax.Int <$> decimal

variable :: Parser Syntax.Expr
variable =
    Syntax.Variable <$> identifier

parens :: Parser Syntax.Expr
parens =
    symbol "(" *> expr <* symbol ")"

---------------------------------------------------------------------------------------------------

parse :: Text -> Either String Syntax.Expr
parse source =
    Parsec.parse toplevel "" source
        & Bifunctor.first Parsec.errorBundlePretty
