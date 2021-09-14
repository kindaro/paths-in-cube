{-# options_ghc -Wno-orphans #-}

module Main (main) where

import Control.Applicative
import Control.Arrow qualified as Arrow
import Control.Comonad
import Control.Comonad.Cofree qualified as Cofree
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Comonad.Trans.Cofree qualified as CofreeTransformer
import Data.Act
import Data.Array (Array)
import Data.Array qualified as Array
import Data.Function
import Data.Function.Memoize
import Data.Functor.Foldable qualified as Recursion
import Data.Map.Lazy (Map)
import Data.Map.Lazy qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Time qualified as Time
import Data.Vector.Unboxed.Sized qualified as Vector
import Data.Vector.Unboxed.Sized (Vector)
import GHC.Exts qualified
import GHC.TypeNats
import Prelude
import Prelude.Unicode
import Relude (bimap, Compose (..))
import Relude.List qualified as List
import Relude qualified
import Generic.Data
import Data.Functor.Classes
import Debug.Trace

main ∷ IO ( )
main = do
  time ← Time.getCurrentTime
  timeMVar ← Relude.newMVar time

  result ← iterator grow (WalkUpToSymmetry (initialWalk @Dimension)) (progressReporter timeMVar)
  print (length result)
  -- Gloss.display (Gloss.InWindow "Nice Window" (200, 200) (10, 10)) Gloss.white (Gloss.Circle 80)

  where
    progressReporter timeMVar (berries, sprouts) = do
      previousTime ← Relude.takeMVar timeMVar
      currentTime ← Time.getCurrentTime
      let differenceInTime = Time.diffUTCTime currentTime previousTime
      Relude.putMVar timeMVar currentTime
      (putStrLn ∘ List.intercalate "\t")
        [ show $ length berries
        , show $ length sprouts
        , Time.formatTime Time.defaultTimeLocale "%H : %M : %0ES" differenceInTime
        , Time.formatTime Time.defaultTimeLocale "%Y %m %d — %H : %M : %0ES" currentTime
        ]

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

instance {-# overlapping #-}
  ( KnownNat dimension
  , HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension))
  ) ⇒ Memoizable [Vector dimension Int] where
  memoize function = findInHierarchicalTree memory
    where
      memory = GHC.Exts.lazy buildHierarchicalTree function

data Pair α = Pair α α deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic, Generic1)

instance Show1 Pair where liftShowsPrec = gliftShowsPrec

cutoff ∷ _ ⇒ Int → Cofree f α → Cofree (Relude.Compose Maybe f) α
cutoff n cofree = Recursion.unfold f (cofree, n)
  where
    f (value :< branches, 0) = value CofreeTransformer.:< Relude.Compose Nothing
    f (value :< branches, n) = value CofreeTransformer.:< Relude.Compose (Just (fmap (, n - 1) branches))

breadth ∷ Cofree Pair α → [[α]]
breadth cofree = Recursion.fold f cofree
  where
    f (value CofreeTransformer.:< Pair leftSubTree rightSubTree) = [value]: zipWith (++) leftSubTree rightSubTree

buildWordTree ∷ ∀ α. (Word → α) → Cofree Pair α
buildWordTree function = Recursion.unfold unfolding 1
  where
    unfolding ∷ Word → CofreeTransformer.CofreeF Pair α Word
    unfolding seed = value CofreeTransformer.:< branch
      where
        value = function seed
        branch = Pair (seed * 2) (seed * 2 + 1)

findInWordTree ∷ Cofree Pair α → Relude.Word → α
findInWordTree _ 0 = error "Only positive indices are accepted, 0 given — cannot answer!"
findInWordTree cofree index = worker cofree (numberOfBinaryDigitsOf index - 1) (index - 2^(numberOfBinaryDigitsOf index - 1))
  where
    worker (extract → value) 0 0 = value
    worker (Cofree.unwrap → Pair leftBranch rightBranch) order index =
      if index ≥ powerOf2
      then worker rightBranch (order - 1) (index - powerOf2)
      else worker leftBranch (order - 1) index
      where powerOf2 = 2^(order - 1)
    worker _ order index = error (show (order, index))

buildIntTree ∷ ∀ α. (Int → α) → Cofree Pair α
buildIntTree function = function 0 :< Pair (buildWordTree (function ∘ negate ∘ fromIntegral)) (buildWordTree (function ∘ fromIntegral))

findInIntTree ∷ Cofree Pair α → Int → α
findInIntTree (valueAt0 :< Pair treeOfNegativeValues treeOfPositiveValues) key = case key `compare` 0 of
  LT → findInWordTree treeOfNegativeValues (negate (fromIntegral key))
  EQ → valueAt0
  GT → findInWordTree treeOfPositiveValues (fromIntegral key)

numberOfBinaryDigitsOf ∷ Word → Relude.Natural
numberOfBinaryDigitsOf = floor ∘ (+1) ∘ logBase @Float 2 ∘ fromIntegral

data Tree dimension α where
  Leaf ∷ Cofree Pair α → Tree 1 α
  Branch ∷ Cofree Pair (Tree (dimension - 1) α) → Tree dimension α

instance {-# overlapping #-} Functor (Tree 1) where
  fmap function (Leaf cofree) = Leaf (fmap function cofree)
  fmap _ (Branch _) = error "Impossible: there are only leaves of dimension 1."

instance (Functor (Tree (dimension - 1))) ⇒ Functor (Tree dimension) where
  fmap function (Branch cofree) = Branch ((fmap ∘ fmap) function cofree)
  fmap _ (Leaf _) = error "Impossible: branches are always of dimension at least 2."

class HierarchicalMemory input memory | input → memory, memory → input where
  buildHierarchicalTree ∷ (input → α) → memory α
  findInHierarchicalTree ∷ memory α → input → α

  memoizeWithHierarchicalTree ∷ (input → α) → input → α
  memoizeWithHierarchicalTree = findInHierarchicalTree ∘ buildHierarchicalTree

instance HierarchicalMemory Int (Cofree Pair) where
  buildHierarchicalTree = buildIntTree
  findInHierarchicalTree = findInIntTree

instance {-# overlapping #-} HierarchicalMemory (Vector 1 Int) (Tree 1) where
  buildHierarchicalTree = Leaf ∘ buildHierarchicalTree ∘ (∘ Vector.singleton)
  findInHierarchicalTree (Leaf cofree) = findInHierarchicalTree cofree ∘ Vector.head
  findInHierarchicalTree (Branch _) = error "Impossible: branches are always of dimension at least 2."

instance
  ( HierarchicalMemory (Vector previousDimension Int) (Tree previousDimension)
  , dimension ~ (1 + previousDimension)
  , previousDimension ~ (dimension - 1)
  ) ⇒ HierarchicalMemory (Vector dimension Int) (Tree dimension) where
  buildHierarchicalTree ∷ ∀ α. (Vector dimension Int → α) → Tree dimension α
  buildHierarchicalTree function = Branch (buildIntTree curriedFunction)
    where
      curriedFunction ∷ Int → Tree (dimension - 1) α
      curriedFunction number = buildHierarchicalTree \ vector → function (number `Vector.cons` vector)

  findInHierarchicalTree ∷ Tree dimension α → (Vector dimension Int → α)
  findInHierarchicalTree (Branch cofree) vector = findInHierarchicalTree (findInIntTree cofree (Vector.head vector)) (Vector.tail vector)
  findInHierarchicalTree (Leaf _) _ = error "Impossible: there are only leaves of dimension 1."

type tube ∘ pipe = Compose tube pipe

instance HierarchicalMemory [Int] (Cofree (Cofree Pair)) where
  buildHierarchicalTree function = Recursion.unfold unfolding id
    where
      unfolding differenceListOfKeys = fruit CofreeTransformer.:< branches
        where
          fruit = function (differenceListOfKeys [ ])
          branches = buildHierarchicalTree \ key → differenceListOfKeys ∘ (key:)

  findInHierarchicalTree (fruit :< _) [ ] = fruit
  findInHierarchicalTree (_ :< branches) (key: keys) = findInHierarchicalTree (findInHierarchicalTree branches key) keys

instance
  ( HierarchicalMemory (Vector dimension Int) (Tree dimension)
  , Functor (Tree dimension)
  ) ⇒ HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension)) where
  buildHierarchicalTree function = Recursion.unfold unfolding id
    where
      unfolding differenceListOfKeys = fruit CofreeTransformer.:< branches
        where
          fruit = function (differenceListOfKeys [ ])
          branches = buildHierarchicalTree \ key → differenceListOfKeys ∘ (key:)

  findInHierarchicalTree (fruit :< _) [ ] = fruit
  findInHierarchicalTree (_ :< branches) (key: keys) = findInHierarchicalTree (findInHierarchicalTree branches key) keys

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

grow ∷ (KnownNat dimension, HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension))) ⇒ WalkUpToSymmetry dimension → Set (Either (WalkUpToSymmetry dimension) (WalkUpToSymmetry dimension))
grow = either (Set.singleton ∘ Left ∘ WalkUpToSymmetry) (Set.map (Right ∘ WalkUpToSymmetry) ∘ Set.fromList) ∘ unfolding ∘ walkUpToSymmetry

iterator
  ∷ ∀ monad underling. (Ord underling, Monad monad)
  ⇒ (underling → Set (Either underling underling))
  → underling
  → ((Set underling, Set underling) → monad ( ))
  → monad [Set underling]
iterator grow seed reportProgress = worker (Set.singleton seed)
  where
    worker ∷ Set underling → monad [Set underling]
    worker growth
      | Set.null growth = return [ ]
      | otherwise = do
          let newGrowth@(berries, sprouts) = (partition ∘ Set.unions ∘ Set.map grow) growth
          reportProgress newGrowth
          lifeGoesOn ← worker sprouts
          return (berries: lifeGoesOn)

partition ∷ (Ord left, Ord right) ⇒ Set (Either left right) → (Set left, Set right)
partition = bimap Set.fromList Set.fromList ∘ List.partitionWith id∘ Set.toList

newtype Permutation dimension = Permutation {indices ∷ Vector dimension Int} deriving (Eq, Ord)

instance Show (Permutation dimension) where show = showVector ∘ indices

instance Semigroup (Permutation dimension) where
  Permutation afterwards <> Permutation first = Permutation (first `Vector.backpermute` afterwards)

instance (Vector.Unbox α, Memoizable (Vector dimension α)) ⇒ Act (Permutation dimension) (Vector dimension α) where
  act Permutation {..} = memoize (flip Vector.backpermute indices)

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
  orbit symmetries = memoize worker
    where
      worker = for symmetries ∘ flip act

instance KnownNat dimension ⇒ Orbit [ ] (HyperoctahedralGroup dimension) [Vector dimension Int] where
  orbit symmetries = getZipList ∘ traverse ((orbit ∘ ZipList) symmetries)

newtype WalkUpToSymmetry dimension = WalkUpToSymmetry {walkUpToSymmetry ∷ Walk dimension} deriving Show

canonicalize
  ∷ ∀ underling action. (Ord underling, Orbit [ ] action underling)
  ⇒ [action] → underling → underling
canonicalize symmetries = minimum ∘ orbit symmetries

representativePath
  ∷ ∀ dimension. (KnownNat dimension, HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension)))
  ⇒ WalkUpToSymmetry dimension → (Vector dimension Int, [Vector dimension Int])
representativePath (WalkUpToSymmetry Walk {..}) = (currentPosition', path')
  where
    path' = memoize (canonicalize (allHyperoctahedralGroup @dimension)) path
    currentPosition' = memoize (canonicalize (allHyperoctahedralGroup @dimension)) currentPosition

instance (KnownNat dimension, HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension))) ⇒ Eq (WalkUpToSymmetry dimension) where
  (==) = (≡) `on` representativePath

instance (KnownNat dimension, HierarchicalMemory [Vector dimension Int] (Cofree (Tree dimension))) ⇒ Ord (WalkUpToSymmetry dimension) where
  compare = compare `on` representativePath
