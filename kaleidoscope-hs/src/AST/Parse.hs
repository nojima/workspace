{-# LANGUAGE ImportQualifiedPost #-}
module AST.Parse
  ( parse
  , Error(..)
  ) where

import Control.Monad.Combinators.Expr qualified as Combinators
import Data.Char qualified as Char
import Data.Function ((&))
import Data.List (foldl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import Text.Megaparsec (Parsec, (<?>))
import Text.Megaparsec qualified as Parsec
import Text.Megaparsec.Char qualified as ParsecChar
import Text.Megaparsec.Char.Lexer qualified as Lexer
import Text.Megaparsec.Error qualified as ParsecError

import AST.Syntax (Name, Expr)
import AST.Syntax qualified as Syntax

--------------------------------------------------------------------------------

type Parser a = Parsec Void Text a

newtype Error = Error Text

--------------------------------------------------------------------------------

space :: Parser ()
space =
  Lexer.space
    ParsecChar.space1
    (Lexer.skipLineComment "//")
    (Lexer.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme =
  Lexer.lexeme space

symbol :: Text -> Parser ()
symbol s =
  () <$ Lexer.symbol space s

float :: Parser Double
float =
  lexeme Lexer.float

keywords :: Set Text
keywords = Set.fromList
  [ "if"
  , "then"
  , "else"
  , "def"
  , "extern"
  ]

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

    alphaNumChars =
      Parsec.takeWhileP
        (Just "alphabets or numbers")
        (\c -> (Char.isAlpha c || Char.isNumber c || c == '_') && Char.isAscii c)
  in
  lexeme (Text.cons <$> alphaChar <*> alphaNumChars)

identifier :: Parser Name
identifier =
  Parsec.try $ Parsec.label "identifier" $ do
    offset <- Parsec.getOffset
    word <- identifierOrKeyword
    if Set.member word keywords then
      let
        actual = ParsecError.Tokens (NonEmpty.fromList (Text.unpack word))
        expected = ParsecError.Label (NonEmpty.fromList "identifier")
        err = ParsecError.TrivialError offset (Just actual) (Set.singleton expected)
      in
      Parsec.parseError err
    else
      return word

--------------------------------------------------------------------------------

parens :: Parser a -> Parser a
parens inner =
  symbol "(" *> inner <* symbol ")"

floatLiteral :: Parser Expr
floatLiteral =
  Syntax.Float <$> float

variable :: Parser Expr
variable =
  Syntax.Variable <$> identifier

function :: Parser Expr
function =
  Syntax.Function
    <$  keyword "def"
    <*> identifier
    <*> parens (variable `Parsec.sepBy` symbol ",")
    <*> expr

extern :: Parser Expr
extern =
  Syntax.Extern
    <$  keyword "extern"
    <*> identifier
    <*> parens (variable `Parsec.sepBy` symbol ",")

call :: Parser Expr
call =
  Syntax.Call
    <$> identifier
    <*> parens (expr `Parsec.sepBy` symbol ",")

factor :: Parser Expr
factor =
  Parsec.choice
    [ floatLiteral
    , function
    , extern
    , Parsec.try call
    , variable
    , parens expr
    ]

expr :: Parser Expr
expr =
  let
    binaryOperator infix_ name op =
      infix_ $ Parsec.label "binary operator" $
        Syntax.BinOp op <$ symbol name
  in
  Combinators.makeExprParser
    factor
    [ [ binaryOperator Combinators.InfixL "*" Syntax.Mul
      , binaryOperator Combinators.InfixL "/" Syntax.Div
      ]
    , [ binaryOperator Combinators.InfixL "+" Syntax.Add
      , binaryOperator Combinators.InfixL "-" Syntax.Sub
      ]
    ]

defn :: Parser Expr
defn =
  Parsec.choice
    [ extern
    , function
    , expr
    ]

toplevel :: Parser [Expr]
toplevel =
     space
  *> Parsec.many (defn <* symbol ";")
  <* Parsec.eof

parse :: Text -> Either Error [Expr]
parse source =
    case Parsec.parse toplevel "<stdin>" source of
        Left errors ->
          let errorMessage = Text.pack (Parsec.errorBundlePretty errors) in
          Left (Error errorMessage)
        Right result ->
          Right result
