module Main where

import Prelude
import Prelude.Unicode
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector
import GHC.TypeNats
import Data.List qualified as List
import Data.Finite
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set (Set)
import Control.Monad.Free
import GHC.Exts
import Data.Foldable qualified as Foldable
import Data.Maybe

main ∷ IO ( )
main = do
  Foldable.traverse_ (putStrLn ∘ show) $ Set.map (head ∘ Set.toList) ∘ Set.fromList ∘ fmap (orbit allHyperoctahedralGroup ∘ path) ∘ retract $ unfold unfolding (initialWalk @4)
  -- Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

vector3d ∷ α → α → α → Vector 3 α
vector3d x y z = Vector.fromTuple (x, y, z)

showVector ∷ Show α ⇒ Vector dimension α → String
showVector vector = "⟨" ++ (unwords ∘ fmap show ∘ Vector.toList) vector ++ "⟩"

sizeOfBox ∷ Num number ⇒ number
sizeOfBox = 2

insideTheBox ∷ Foldable foldable ⇒ foldable ℤ → Bool
insideTheBox = all (\ x → 0 ≤ x ∧ x < sizeOfBox)

for ∷ Functor functor ⇒ functor α → (α → β) → functor β
for = flip fmap

type key ⇸ value = Map.Map key value

unitVectors ∷ ∀ dimension. KnownNat dimension ⇒ Vector dimension (Vector dimension ℤ)
unitVectors = Vector.zipWith (\ vector replacement → vector Vector.// [replacement]) 0 bitsToSet
  where
    bitsToSet ∷ Vector dimension (Finite dimension, ℤ)
    bitsToSet = Vector.zip (Vector.enumFromN 0) 1

directions ∷ ∀ dimension. KnownNat dimension ⇒ [Vector dimension ℤ]
directions = Vector.toList (unitVectors Vector.++ fmap negate unitVectors)

simpleStep ∷ KnownNat dimension ⇒ Vector dimension ℤ → [Vector dimension ℤ]
simpleStep = filter insideTheBox ∘ for directions ∘ (+)

nonRepeatingStep ∷ KnownNat dimension ⇒ Set (Vector dimension ℤ) → Vector dimension ℤ → [Vector dimension ℤ]
nonRepeatingStep visitedVectors = filter (not ∘ (`Set.member` visitedVectors)) ∘ simpleStep

data Walk (dimension ∷ Nat) = Walk
  { visitedVectors ∷ Set (Vector dimension ℤ)
  , path ∷ [Vector dimension ℤ]
  , currentPosition ∷ Vector dimension ℤ
  } deriving (Eq, Ord)

instance Show (Walk dimension) where
  show = List.intercalate " → " ∘ fmap showVector ∘ reverse ∘ path

initialWalk ∷ KnownNat dimension ⇒ Walk dimension
initialWalk = Walk
  { visitedVectors = Set.singleton 0
  , path = [0]
  , currentPosition = 0
  }

step ∷ KnownNat dimension ⇒ Walk dimension → [Walk dimension]
step Walk {..} = do
  nextPosition ← nonRepeatingStep visitedVectors currentPosition
  return Walk
    { visitedVectors = nextPosition `Set.insert` visitedVectors
    , path = nextPosition: path
    , currentPosition = nextPosition }

unfolding ∷ ∀ dimension. KnownNat dimension ⇒ Walk dimension → Either (Walk dimension) [Walk dimension]
unfolding walk@Walk {..} = case step walk of
  [ ] → if Set.size visitedVectors ≡ sizeOfBox ^ fromIntegral @_ @Int (natVal' (proxy# @dimension)) then Left walk else Right [ ]
  possibleNextWalks → Right possibleNextWalks

newtype Permutation dimension = Permutation {indices ∷ Vector dimension Int} deriving (Eq, Ord)

instance Show (Permutation dimension) where show = showVector ∘ indices

allPermutations ∷ ∀ dimension. KnownNat dimension ⇒ [Permutation dimension]
allPermutations = (fmap Permutation ∘ catMaybes ∘ fmap Vector.fromList ∘ List.permutations)
  [0.. fromIntegral (natVal' (proxy# @dimension)) - 1]

data HyperoctahedralGroup (dimension ∷ Nat) = HyperoctahedralGroup
  {permutation ∷ Permutation dimension
  , reflexion ∷ Vector dimension Bool
 } deriving (Eq, Ord)

instance Show (HyperoctahedralGroup dimension) where
  show HyperoctahedralGroup {..} = show permutation ++ for (Vector.toList reflexion) \ bit → if bit then '↑' else '↓'

allHyperoctahedralGroup ∷ ∀ dimension. KnownNat dimension ⇒ [HyperoctahedralGroup dimension]
allHyperoctahedralGroup = do
  permutation ← allPermutations
  reflexion ← Vector.replicateM [True, False]
  return HyperoctahedralGroup {..}

applyAtIndex ∷ Finite dimension → (α → α) → Vector dimension α → Vector dimension α
applyAtIndex index function vector = vector Vector.// [(index, function (Vector.index vector index))]

applySymmetry ∷ ∀ dimension. HyperoctahedralGroup dimension → Vector dimension ℤ → Vector dimension ℤ 
applySymmetry HyperoctahedralGroup {..} =
  let
    rotate = (`Vector.backpermute` indices permutation)
    reflect = fmap (`mod` sizeOfBox) ∘ Vector.zipWith ($) (for reflexion \ bit → if bit then id else \ x → -x + 1)
  in rotate ∘ reflect

newtype WalkUpToSymmetry dimension = WalkUpToSymmetry (Walk dimension)

orbit ∷ ∀ dimension. [HyperoctahedralGroup dimension] → [Vector dimension ℤ] → Set [Vector dimension ℤ]
orbit symmetries = Set.fromList ∘ for (fmap applySymmetry symmetries) ∘ for
