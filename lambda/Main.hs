{-# OPTIONS -Wall -Werror #-}
module Main(main) where

import Lambda

main :: IO ()
main =
    let
        zero = ZeroTerm (Location 1)
        one = SuccTerm (Location 2) zero
        true = (TrueTerm (Location 3))
        if_ = IfTerm (Location 3) true one zero
    in
    do
        putStrLn $ show $ evalOne zero
        putStrLn $ show $ evalOne if_
        putStrLn $ show $ eval if_
