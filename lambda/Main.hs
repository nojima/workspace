{-# OPTIONS -Wall -Werror #-}
module Main(main) where

import Syntax
import Eval

main :: IO ()
main =
    let
        zero = Zero (Location 1)
        one = Succ (Location 2) zero
        true = (True_ (Location 3))
        if_ = If (Location 3) true one zero
    in
    do
        putStrLn $ show $ evalOne zero
        putStrLn $ show $ evalOne if_
        putStrLn $ show $ eval if_
