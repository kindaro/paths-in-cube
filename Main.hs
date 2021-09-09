module Main where

import Prelude
import Prelude.Unicode
import Numeric.Natural.Unicode
import Data.Function
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector

import Data.List qualified as List
import Graphics.Gloss qualified as Gloss
import Data.Finite
import Test.Tasty.QuickCheck
import Test.Tasty.Bench

main = Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

unitVectors ∷ ∀ dimension. Vector dimension (Vector dimension ℤ)
unitVectors = Vector.replicate 0 `Vector.//` bitsToSet
  where bitsToSet = zip finites (repeat 1)
