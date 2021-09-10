{-# options_ghc -Wno-orphans #-}

module Main (main) where

import Prelude
import Prelude.Unicode
import Data.Vector.Unboxed.Sized (Vector)
import Data.Vector.Unboxed.Sized qualified as Vector
import GHC.TypeNats
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Set (Set)
import Control.Monad.Free
import GHC.Exts qualified
import Data.Maybe
import Data.Array qualified as Array
import Data.Array (Array, Ix)
import Debug.Trace
import Data.Act
import Control.Lens qualified as Lens
import Data.Function.Memoize
import Control.Arrow qualified as Arrow
import Control.Applicative

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

type Dimension = 2
type SizeOfTheBox = 6

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
simpleStep = filter isInsideTheBox ∘ for directions ∘ {-# scc "vectorAddition" #-} (+)

nonRepeatingStep ∷ KnownNat dimension ⇒ Set (Vector dimension Int) → Vector dimension Int → [Vector dimension Int]
nonRepeatingStep visitedVectors = filter notVisited ∘ simpleStep
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

allPermutations ∷ ∀ dimension. KnownNat dimension ⇒ [Permutation dimension]
allPermutations = (fmap Permutation ∘ catMaybes ∘ fmap Vector.fromList ∘ List.permutations)
  [0.. get @dimension reifiedNat - 1]

data HyperoctahedralGroup (dimension ∷ Nat) = HyperoctahedralGroup
  {permutation ∷ Permutation dimension
  , reflexion ∷ Vector dimension Bool
 } deriving (Eq, Ord)

instance Show (HyperoctahedralGroup dimension) where
  show HyperoctahedralGroup {..} = show permutation ++ for (Vector.toList reflexion) \ bit → if bit then '↑' else '↓'

instance Semigroup (HyperoctahedralGroup dimension) where
  afterwards <> first = HyperoctahedralGroup
    { permutation = permutation afterwards <> permutation first
    , reflexion = Vector.zipWith (≢) (reflexion afterwards) (reflexion first)
    }

instance (Integral number, Vector.Unbox number) ⇒ Act (HyperoctahedralGroup dimension) (Vector dimension number) where
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

newtype FormalHyperoctahedralGroup (dimension ∷ Nat) = FormalHyperoctahedralGroup Int deriving (Show, Eq, Ord, Num, Ix)

whelving ∷ ∀ dimension. KnownNat dimension ⇒ Lens.Iso' (HyperoctahedralGroup dimension) (FormalHyperoctahedralGroup dimension)
whelving = Lens.iso getIndex getValue
  where
    getIndex value = case List.elemIndex value allHyperoctahedralGroup of
      Just index → FormalHyperoctahedralGroup index
      Nothing → error "Impossible: `HyperoctahedralGroup` is closed."
    getValue (FormalHyperoctahedralGroup index) = allHyperoctahedralGroup List.!! index

instance KnownNat dimension ⇒ Semigroup (FormalHyperoctahedralGroup dimension) where
  afterwards <> first = Lens.view whelving (Lens.view (Lens.from whelving) afterwards <> Lens.view (Lens.from whelving) first)

instance
  ( KnownNat dimension, Act (HyperoctahedralGroup dimension) (Vector dimension number)
  ) ⇒ Act (FormalHyperoctahedralGroup dimension) (Vector dimension number) where
  act = act ∘ Lens.view (Lens.from whelving)

newtype WalkUpToSymmetry dimension = WalkUpToSymmetry (Walk dimension)

orbit ∷ (Act action underling, Traversable traversable, Memoizable underling) ⇒ [action] → traversable underling → [traversable underling]
orbit actions = getZipList ∘ traverse (memoize (for (ZipList actions) ∘ flip act))
