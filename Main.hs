{-# options_ghc -Wno-orphans #-}

module Main (main) where

import Prelude
import Prelude.Unicode
import Data.Vector.Unboxed.Sized (Vector)
import Data.Vector.Unboxed.Sized qualified as Vector
import GHC.TypeNats
import qualified Relude.List as List
import Data.Set qualified as Set
import Data.Set (Set)
import Control.Monad.Free
import GHC.Exts qualified
import Data.Maybe
import Data.Array qualified as Array
import Data.Array (Array)
import Debug.Trace
import Data.Act
import Data.Function.Memoize
import Control.Arrow qualified as Arrow
import Control.Applicative
import Data.Function

main ∷ IO ( )
main = do
  print ∘ length $ Set.map (head ∘ Set.toList) ∘ Set.fromList ∘ fmap (Set.fromList ∘ orbit (allHyperoctahedralGroup @Dimension) ∘ path) ∘ retract $ unfold unfolding (initialWalk @Dimension)
  -- Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

newtype ReifiedNat (nat ∷ Nat) number = ReifiedNat {get ∷ number} deriving (Show, Eq, Ord)

reifiedNat ∷ ∀ nat number. (KnownNat nat, Num number) ⇒ ReifiedNat nat number
reifiedNat = ReifiedNat {get = fromIntegral (natVal' (GHC.Exts.proxy# @nat))}

vector3d ∷ Vector.Unbox α ⇒ α → α → α → Vector 3 α
vector3d x y z = Vector.fromTuple (x, y, z)

showVector ∷ (Show α, Vector.Unbox α) ⇒ Vector dimension α → String
showVector vector = "⟨" ++ (unwords ∘ fmap show ∘ Vector.toList) vector ++ "⟩"

type Dimension = 4
type SizeOfTheBox = 2

sizeOfTheBox ∷ Num number ⇒ number
sizeOfTheBox = get (reifiedNat @SizeOfTheBox)


theBox ∷ (Num number, Enum number, Vector.Unbox number, KnownNat dimension) ⇒ [Vector dimension number]
theBox = Vector.replicateM [0.. sizeOfTheBox - 1]

isInsideTheBox ∷ Vector dimension Int → Bool
isInsideTheBox = Vector.all (\ x → 0 ≤ x ∧ x < sizeOfTheBox)

instance KnownNat dimension ⇒ Memoizable (Vector dimension Int) where
  memoize ∷ ∀ output. (Vector dimension Int → output) → Vector dimension Int → output
  memoize function = \ input → if isInsideTheBox input
    then memory Array.! encodeVector input
    else function input
    where
      memory ∷ Int ⇸ output
      memory = Array.array bounds contents
        where
          bounds = (encodeVector @dimension (head theBox), encodeVector @dimension (last theBox))
          contents = fmap (encodeVector Arrow.&&& function) theBox

      -- | I could simply index the array by vectors, since they have the `Ix`
      -- interface. But it turns out to be twice faster to encode those vectors
      -- to `Int` and index the array by that `Int`.
      encodeVector ∷ ∀ dimension'. KnownNat dimension' ⇒ Vector dimension' Int → Int
      encodeVector = Vector.sum ∘ polynomial
        where
          polynomial vector = Vector.zipWith (\ digit power → digit * get @SizeOfTheBox reifiedNat^power) vector (enumFrom0 @Int)

enumFrom0 ∷ ∀ number length. (Num number, Enum number, Vector.Unbox number, KnownNat length) ⇒ Vector length number
enumFrom0 = Vector.enumFromN 0

for ∷ Functor functor ⇒ functor α → (α → β) → functor β
for = flip fmap

type key ⇸ value = Array key value

unitVectors ∷ ∀ dimension. KnownNat dimension ⇒ Vector dimension (Vector dimension Int)
unitVectors = Vector.map makeUnitVector enumFrom0
  where
    makeUnitVector ∷ Int → Vector dimension Int
    makeUnitVector bit = 0 Vector.// [(fromIntegral bit, 1)]

directions ∷ ∀ dimension. KnownNat dimension ⇒ [Vector dimension Int]
directions = Vector.toList (unitVectors Vector.++ Vector.map negate unitVectors)

simpleStep ∷ KnownNat dimension ⇒ Vector dimension Int → [Vector dimension Int]
simpleStep = filter isInsideTheBox ∘ for directions ∘ (+)

nonRepeatingStep ∷ KnownNat dimension ⇒ Set (Vector dimension Int) → Vector dimension Int → [Vector dimension Int]
nonRepeatingStep visitedVectors = filter notVisited ∘ memoize simpleStep
  where
    notVisited = not ∘ (`Set.member` visitedVectors)

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
  [ ] → if Set.size visitedVectors ≡ sizeOfTheBox ^ get @dimension @Int reifiedNat then Left walk else Right [ ]
  possibleNextWalks → Right possibleNextWalks

newtype Permutation dimension = Permutation {indices ∷ Vector dimension Int} deriving (Eq, Ord)

instance Show (Permutation dimension) where show = showVector ∘ indices

instance Semigroup (Permutation dimension) where
  Permutation afterwards <> Permutation first = Permutation (first `Vector.backpermute` afterwards)

instance Vector.Unbox α ⇒ Act (Permutation dimension) (Vector dimension α) where
  Permutation {..} `act` vector = vector `Vector.backpermute` indices

identityPermutation ∷ ∀ dimension. KnownNat dimension ⇒ Permutation dimension
identityPermutation = Permutation enumFrom0

permutations ∷ ∀ dimension α. (Vector.Unbox α, KnownNat dimension) ⇒ Vector dimension α → [Vector dimension α]
permutations = catMaybes ∘ fmap Vector.fromList ∘ List.permutations ∘ Vector.toList

allPermutations ∷ ∀ dimension. KnownNat dimension ⇒ [Permutation dimension]
allPermutations = (fmap Permutation ∘ permutations ∘ indices) identityPermutation

data HyperoctahedralGroup (dimension ∷ Nat) = HyperoctahedralGroup
  { permutation ∷ Permutation dimension
  , reflexion ∷ Vector dimension Bool
 } deriving (Eq, Ord)

instance Show (HyperoctahedralGroup dimension) where
  show HyperoctahedralGroup {..} = show permutation ++ for (Vector.toList reflexion) \ bit → if bit then '↑' else '↓'

instance Semigroup (HyperoctahedralGroup dimension) where
  afterwards <> first = HyperoctahedralGroup
    { permutation = permutation afterwards <> permutation first
    , reflexion = Vector.zipWith (≢) (reflexion afterwards) (reflexion first)
    }

instance
  ( Integral number, Vector.Unbox number, Memoizable (Vector dimension number), KnownNat dimension
  ) ⇒ Act (HyperoctahedralGroup dimension) (Vector dimension number) where
  act HyperoctahedralGroup {..}
    = Vector.map ((`mod` sizeOfTheBox) ∘ uncurry maybeReflect)
    ∘ Vector.zip reflexion
    ∘ act permutation
      where
        maybeReflect ∷ Bool → number → number
        maybeReflect reflect = if reflect then id else \ x → -x + sizeOfTheBox

allHyperoctahedralGroup ∷ ∀ dimension. KnownNat dimension ⇒ [HyperoctahedralGroup dimension]
allHyperoctahedralGroup = do
  permutation ← allPermutations
  reflexion ← Vector.replicateM [True, False]
  return HyperoctahedralGroup {..}

class Orbit functor action underling where
  orbit ∷ functor action → underling → functor underling

instance (Functor functor, KnownNat dimension) ⇒ Orbit functor (HyperoctahedralGroup dimension) (Vector dimension Int) where
  orbit symmetries = for symmetries ∘ flip act

instance KnownNat dimension ⇒ Orbit [ ] (HyperoctahedralGroup dimension) [Vector dimension Int] where
  orbit symmetries = getZipList ∘ traverse ((memoize ∘ orbit ∘ ZipList) symmetries)

instance KnownNat dimension ⇒ Orbit [ ] (HyperoctahedralGroup dimension) (Walk dimension) where
  orbit symmetries = getZipList ∘ traverseWalk ((orbit ∘ ZipList) symmetries)

traverseWalk
  ∷ Applicative applicative
  ⇒ (Vector dimension Int → applicative (Vector dimension Int)) → Walk dimension → applicative (Walk dimension)
traverseWalk function Walk {..} = pure Walk
  <*> (fmap Set.fromList ∘ traverse function ∘ Set.toList) visitedVectors
  <*> traverse function path
  <*> function currentPosition

representative
  ∷ ∀ underling action. (Ord underling, Orbit [ ] action underling)
  ⇒ [action] → underling → underling
representative symmetries = minimum ∘ orbit symmetries

newtype WalkUpToSymmetry dimension = WalkUpToSymmetry {walkUpToSymmetry ∷ Walk dimension} deriving Show

instance KnownNat dimension ⇒ Eq (WalkUpToSymmetry dimension) where
  (==) = (≡) `on` representative (allHyperoctahedralGroup @dimension) ∘ walkUpToSymmetry
