module Calc.Pretty where

import qualified Data.Text as T

class Pretty a where
    pretty :: a -> T.Text

instance Pretty Integer where
    pretty i = T.pack (show i)
