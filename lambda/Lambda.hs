{-# OPTIONS -Wall -Werror #-}
module Lambda
    ( Term(..)
    , Location(..)
    , eval
    )
    where

import Data.Either()

data Term
    = TrueTerm Location
    | FalseTerm Location
    | IfTerm Location Term Term Term
    | ZeroTerm Location
    | SuccTerm Location Term
    | PredTerm Location Term
    | IsZeroTerm Location Term
    deriving (Show)

data Location
    = Location Int

instance Show Location where
    show (Location line) = "L" ++ show line

dummyLocation :: Location
dummyLocation = Location 0

data EvalError
    = EvalError String
    deriving (Show)

type Result a
    = Either EvalError a

isNumericValue :: Term -> Bool
isNumericValue term =
    case term of
        ZeroTerm _ -> True
        SuccTerm _ term' -> isNumericValue term'
        _ -> False

{-
isValue :: Term -> Bool
isValue term =
    case term of
        TrueTerm _ -> True
        FalseTerm _ -> True
        _ -> isNumericValue term
-}

evalOne :: Term -> Result Term
evalOne term =
    case term of
        IfTerm loc condTerm thenTerm elseTerm ->
            case condTerm of
                TrueTerm _ ->
                    Right thenTerm
                FalseTerm _ ->
                    Right elseTerm
                _ ->
                    IfTerm loc
                        <$> evalOne condTerm
                        <*> pure thenTerm
                        <*> pure elseTerm

        SuccTerm loc inner ->
            SuccTerm loc <$> evalOne inner

        PredTerm loc inner ->
            case inner of
                ZeroTerm _ ->
                    Right $ ZeroTerm dummyLocation
                SuccTerm _ num | isNumericValue num ->
                    Right num
                _ ->
                    PredTerm loc <$> evalOne inner

        IsZeroTerm loc inner ->
            case inner of
                ZeroTerm _ ->
                    Right $ TrueTerm dummyLocation
                SuccTerm _ num | isNumericValue num ->
                    Right $ FalseTerm dummyLocation
                _ ->
                    IsZeroTerm loc <$> evalOne inner

        _ ->
            Left (EvalError "no rule applies")

eval :: Term -> Term
eval term =
    case evalOne term of
        Right term' ->
            eval term'
        Left _ ->
            term
