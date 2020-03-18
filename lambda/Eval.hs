{-# OPTIONS -Wall -Werror #-}
module Eval
    ( EvalError
    , Result
    , eval
    , evalOne
    )
    where

import Data.Either()
import qualified Syntax

data EvalError
    = EvalError String
    deriving (Show)

type Result a
    = Either EvalError a

dummyLocation :: Syntax.Location
dummyLocation = Syntax.Location 0

isNumericValue :: Syntax.Term -> Bool
isNumericValue term =
    case term of
        Syntax.Zero _ -> True
        Syntax.Succ _ term' -> isNumericValue term'
        _ -> False

{-
isValue :: Syntax.Term -> Bool
isValue term =
    case term of
        Syntax.True_ _ -> True
        Syntax.False_ _ -> True
        _ -> isNumericValue term
-}

evalOne :: Syntax.Term -> Result Syntax.Term
evalOne term =
    case term of
        Syntax.If loc condTerm thenTerm elseTerm ->
            case condTerm of
                Syntax.True_ _ ->
                    Right thenTerm
                Syntax.False_ _ ->
                    Right elseTerm
                _ ->
                    Syntax.If loc
                        <$> evalOne condTerm
                        <*> pure thenTerm
                        <*> pure elseTerm

        Syntax.Succ loc inner ->
            Syntax.Succ loc <$> evalOne inner

        Syntax.Pred loc inner ->
            case inner of
                Syntax.Zero _ ->
                    Right $ Syntax.Zero dummyLocation
                Syntax.Succ _ num | isNumericValue num ->
                    Right num
                _ ->
                    Syntax.Pred loc <$> evalOne inner

        Syntax.IsZero loc inner ->
            case inner of
                Syntax.Zero _ ->
                    Right $ Syntax.True_ dummyLocation
                Syntax.Succ _ num | isNumericValue num ->
                    Right $ Syntax.False_ dummyLocation
                _ ->
                    Syntax.IsZero loc <$> evalOne inner

        _ ->
            Left (EvalError "no rule applies")

eval :: Syntax.Term -> Syntax.Term
eval term =
    case evalOne term of
        Right term' ->
            eval term'
        Left _ ->
            term
