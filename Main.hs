module Main (main) where

import Prelude
import Prelude.Unicode
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vector
import GHC.TypeNats
import Data.List qualified as List
import Data.Finite
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Set (Set)
import Control.Monad.Free
import GHC.Exts qualified
import Data.Foldable qualified as Foldable
import Data.Maybe
import Control.Monad
import Data.Array qualified as Array
import Data.Array (Array, Ix)
import Debug.Trace
import Data.Bifunctor

main ∷ IO ( )
main = do
  print ∘ length $ Set.map (head ∘ Set.toList) ∘ Set.fromList ∘ fmap (orbit (Array.indices hyperoctahedralGroupIndex) ∘ path) ∘ retract $ unfold unfolding (initialWalk @4)
  -- Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

newtype ReifiedNat (nat ∷ Nat) number = ReifiedNat {get ∷ number} deriving (Show, Eq, Ord)

reifiedNat ∷ ∀ nat number. (KnownNat nat, Num number) ⇒ ReifiedNat nat number
reifiedNat = ReifiedNat {get = fromIntegral (natVal' (GHC.Exts.proxy# @nat))}

applyAtIndex ∷ Finite length → (α → α) → Vector length α → Vector length α
applyAtIndex index function vector = vector Vector.// [(index, function (Vector.index vector index))]

vector3d ∷ α → α → α → Vector 3 α
vector3d x y z = Vector.fromTuple (x, y, z)

showVector ∷ Show α ⇒ Vector dimension α → String
showVector vector = "⟨" ++ (unwords ∘ fmap show ∘ Vector.toList) vector ++ "⟩"

type SizeOfBox = 2

sizeOfBox ∷ Num number ⇒ number
sizeOfBox = get (reifiedNat @SizeOfBox)

insideTheBox ∷ Foldable foldable ⇒ foldable Int → Bool
insideTheBox = all (\ x → 0 ≤ x ∧ x < sizeOfBox)

for ∷ Functor functor ⇒ functor α → (α → β) → functor β
for = flip fmap

type key ⇸ value = Array key value

unitVectors ∷ ∀ dimension. KnownNat dimension ⇒ Vector dimension (Vector dimension Int)
unitVectors = Vector.zipWith (\ vector replacement → vector Vector.// [replacement]) 0 bitsToSet
  where
    bitsToSet ∷ Vector dimension (Finite dimension, Int)
    bitsToSet = Vector.zip (Vector.enumFromN 0) 1

directions ∷ ∀ dimension. KnownNat dimension ⇒ [Vector dimension Int]
directions = Vector.toList (unitVectors Vector.++ fmap negate unitVectors)

simpleStep ∷ KnownNat dimension ⇒ Vector dimension Int → [Vector dimension Int]
simpleStep = filter insideTheBox ∘ for directions ∘ (+)

nonRepeatingStep ∷ KnownNat dimension ⇒ Set (Vector dimension Int) → Vector dimension Int → [Vector dimension Int]
nonRepeatingStep visitedVectors = filter (not ∘ (`Set.member` visitedVectors)) ∘ simpleStep

data Walk (dimension ∷ Nat) = Walk
  { visitedVectors ∷ Set (Vector dimension Int)
  , path ∷ [Vector dimension Int]
  , currentPosition ∷ Vector dimension Int
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
  [ ] → if Set.size visitedVectors ≡ sizeOfBox ^ get @dimension @Int reifiedNat then Left walk else Right [ ]
  possibleNextWalks → Right possibleNextWalks

newtype Permutation dimension = Permutation {indices ∷ Vector dimension Int} deriving (Eq, Ord)

instance Show (Permutation dimension) where show = showVector ∘ indices

allPermutations ∷ ∀ dimension. KnownNat dimension ⇒ [Permutation dimension]
allPermutations = (fmap Permutation ∘ catMaybes ∘ fmap Vector.fromList ∘ List.permutations)
  [0.. get @dimension reifiedNat - 1]

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

newtype FormalHyperoctahedralGroup (dimension ∷ Nat) = FormalHyperoctahedralGroup Int deriving (Show, Eq, Ord, Num, Ix)

fromList ∷ (Num index, Ix index) ⇒ [α] → Array index α
fromList list = Array.listArray (0, List.genericLength list - 1) list

hyperoctahedralGroupIndex
  ∷ ∀ dimension. KnownNat dimension
  ⇒ Array (FormalHyperoctahedralGroup dimension) (HyperoctahedralGroup dimension)
hyperoctahedralGroupIndex = fromList (allHyperoctahedralGroup @dimension)
{-# specialize hyperoctahedralGroupIndex ∷ Array (FormalHyperoctahedralGroup 2) (HyperoctahedralGroup 2) #-}
{-# specialize hyperoctahedralGroupIndex ∷ Array (FormalHyperoctahedralGroup 3) (HyperoctahedralGroup 3) #-}

applySymmetry
  ∷ ∀ dimension. KnownNat dimension
  ⇒ FormalHyperoctahedralGroup dimension → Vector dimension Int → Vector dimension Int
applySymmetry identifier =
  let HyperoctahedralGroup {..} = hyperoctahedralGroupIndex Array.! identifier
  in rotate permutation ∘ reflect reflexion
  where
    rotate permutation = (`Vector.backpermute` indices permutation)
    reflect reflexion = fmap (`mod` sizeOfBox) ∘ Vector.zipWith ($) (for reflexion \ bit → if bit then id else \ x → -x + 1)

applySymmetryMemoized ∷
  ∀ dimension. KnownNat dimension
  ⇒ FormalHyperoctahedralGroup dimension → Vector dimension Int → Vector dimension Int
applySymmetryMemoized symmetry vector = symmetries Array.! (symmetry, encodeVector vector)

newtype EncodedVector (dimension ∷ Nat) (sizeOfBox ∷ Nat) = EncodedVector Int deriving (Show, Eq, Ord, Num, Ix)

encodeVector
  ∷ ∀ dimension sizeOfBox. (KnownNat dimension, KnownNat sizeOfBox)
  ⇒ Vector dimension Int → EncodedVector dimension sizeOfBox
encodeVector = EncodedVector ∘ sum ∘ polynomial
  where
    polynomial vector = Vector.zipWith (\ digit power → digit * get @sizeOfBox reifiedNat^power) vector (Vector.enumFromN (0 ∷ Int))

diagonal x = (x, x)

symmetries
  ∷ ∀ dimension. KnownNat dimension
  ⇒ (FormalHyperoctahedralGroup dimension, EncodedVector dimension 3) ⇸ Vector dimension Int
symmetries = trace "symmetries entered" array
  where
    box ∷ [Vector dimension Int]
    box = Vector.replicateM [0.. sizeOfBox - 1]
    domain = pure (,) <*> Array.indices hyperoctahedralGroupIndex <*> box
    values = fmap (uncurry applySymmetry) domain
    domain' = (fmap ∘ fmap) encodeVector domain
    array = Array.array (head domain', last domain') (zip domain' values)

{-# specialize symmetries ∷ (FormalHyperoctahedralGroup 2, EncodedVector 2 3) ⇸ Vector 2 Int #-}
{-# specialize symmetries ∷ (FormalHyperoctahedralGroup 3, EncodedVector 3 3) ⇸ Vector 3 Int #-}

newtype WalkUpToSymmetry dimension = WalkUpToSymmetry (Walk dimension)

orbit ∷ ∀ dimension. KnownNat dimension ⇒ [FormalHyperoctahedralGroup dimension] → [Vector dimension Int] → Set [Vector dimension Int]
orbit symmetries = Set.fromList ∘ for (fmap applySymmetryMemoized symmetries) ∘ for
