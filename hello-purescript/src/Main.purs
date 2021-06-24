module Main where

import Prelude

import Data.List (List, range, filter)
import Data.Foldable (sum)
import Effect (Effect)
import Effect.Console (log)

ns :: List Int
ns = range 0 999

multiples :: List Int
multiples = filter (\n -> mod n 3 == 0 || mod n 5 == 0) ns

answer :: Int
answer = sum multiples

main :: Effect Unit
main = do
  log ("The answer is " <> show answer)
