module Main where

import Prelude
import Prelude.Unicode
import Numeric.Natural.Unicode
import Data.Function
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector
import GHC.TypeNats
import Data.List qualified as List
import Graphics.Gloss qualified as Gloss
import Data.Finite
import Test.Tasty.QuickCheck
import Test.Tasty.Bench
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set (Set)
import Control.Monad.Free
import GHC.Exts
import Data.Foldable qualified as Foldable
import Text.Groom

main = do
  putStrLn ∘ groom ∘ fmap path ∘ retract $ unfold unfolding (initialWalk @3)
  -- Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

sizeOfBox ∷ Num number ⇒ number
sizeOfBox = 2

insideTheBox ∷ _ ⇒ foldable ℤ → Bool
insideTheBox = all (\ x → 0 ≤ x ∧ x < sizeOfBox)

for = flip fmap
type key ⇸ value = Map.Map key value

unitVectors ∷ ∀ dimension. KnownNat dimension ⇒ Vector dimension (Vector dimension ℤ)
unitVectors = Vector.zipWith (\ vector replacement → vector Vector.// [replacement]) 0 bitsToSet
  where
    bitsToSet ∷ Vector dimension (Finite dimension, ℤ)
    bitsToSet = Vector.zip (Vector.enumFromN 0) 1

directions ∷ ∀ dimension. KnownNat dimension ⇒ [Vector dimension ℤ]
directions = Vector.toList (unitVectors Vector.++ fmap negate unitVectors)

simpleStep ∷ _ ⇒ Vector dimension ℤ → [Vector dimension ℤ]
simpleStep = filter insideTheBox ∘ for directions ∘ (+)

nonRepeatingStep ∷ _ ⇒ Set (Vector dimension ℤ) → Vector dimension ℤ → [Vector dimension ℤ]
nonRepeatingStep visitedVectors = filter (not ∘ (`Set.member` visitedVectors)) ∘ simpleStep

data Walk (dimension ∷ Nat) = Walk
  { visitedVectors ∷ Set (Vector dimension ℤ)
  , path ∷ [Vector dimension ℤ]
  , currentPosition ∷ Vector dimension ℤ
  } deriving (Show, Read, Eq, Ord)

initialWalk ∷ _ ⇒ Walk dimension
initialWalk = Walk
  { visitedVectors = Set.singleton 0
  , path = [0]
  , currentPosition = 0
  }

step ∷ _ ⇒ Walk dimension → [Walk dimension]
step Walk {..} = do
  nextPosition ← nonRepeatingStep visitedVectors currentPosition
  return Walk
    { visitedVectors = nextPosition `Set.insert` visitedVectors
    , path = nextPosition: path
    , currentPosition = nextPosition }

unfolding ∷ ∀ dimension. _ ⇒ Walk dimension → Either (Walk dimension) [Walk dimension]
unfolding walk@Walk {..} = case step walk of
  [ ] → if Set.size visitedVectors ≡ sizeOfBox ^ fromIntegral (natVal' (proxy# @dimension)) then Left walk else Right [ ]
  possibleNextWalks → Right possibleNextWalks
