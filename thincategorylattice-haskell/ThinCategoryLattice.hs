{- |
Module      : ThinCategoryLattice
Description : Connected Categorical and Geometric Pipeline of Subobject Lattices
Author      : Shivansh Singh
Date        : March 2026

A unified, end-to-end executable pipeline connecting:
  Lattice Hierarchy (§2, §3)
    ──► Loewy Sieve & Travel Experience Odometer (§4, §5)
    ──► Chained Morphisms & Crystalline Associahedra Tower (§6)
    ──► Thin Morphism Diagram Collapse & Lie Root Energy (§7)
-}

module ThinCategoryLattice where

import Data.List (find, nub, subsequences)
import Data.Maybe (isJust)

--------------------------------------------------------------------------------
-- 1. POSETS AS THIN CATEGORIES & GALOIS ADJUNCTIONS (§2)
--------------------------------------------------------------------------------

class Eq a => Poset a where
    (<=:) :: a -> a -> Bool

class Poset a => Lattice a where
    (/\) :: a -> a -> a
    (\/) :: a -> a -> a

class Lattice a => BoundedLattice a where
    bottom :: a
    top    :: a

-- | Subsingleton Hom-set: |Hom(a, b)| <= 1 (unique arrow iff x <= y)
newtype ThinHom a b = ThinHom () deriving (Eq, Show)

thinHom :: Poset a => a -> a -> Maybe (ThinHom a b)
thinHom x y = if x <=: y then Just (ThinHom ()) else Nothing

composeThin :: ThinHom b c -> ThinHom a b -> ThinHom a c
composeThin _ _ = ThinHom ()

-- | Galois Adjunction F -| G: F(x) <= y <=> x <= G(y)
data GaloisConnection a b = GaloisConnection
    { leftAdjoint  :: a -> b
    , rightAdjoint :: b -> a
    }

isGalois :: (Poset a, Poset b) => GaloisConnection a b -> [a] -> [b] -> Bool
isGalois (GaloisConnection f g) xs ys =
    all (\(x, y) -> (f x <=: y) == (x <=: g y)) [(x, y) | x <- xs, y <- ys]

newtype ClosureOperator a = ClosureOperator (a -> a)

galoisToClosure :: GaloisConnection a b -> ClosureOperator a
galoisToClosure (GaloisConnection f g) = ClosureOperator (g . f)

isClosure :: Poset a => ClosureOperator a -> [a] -> Bool
isClosure (ClosureOperator cl) xs =
    all (\x -> x <=: cl x) xs &&
    all (\(x, y) -> not (x <=: y) || cl x <=: cl y) [(x, y) | x <- xs, y <- xs] &&
    all (\x -> cl (cl x) == cl x) xs

--------------------------------------------------------------------------------
-- 2. SUBMODULAR RANK DEFECTS & TOR_0 (§3)
--------------------------------------------------------------------------------

-- | Submodular Defect Delta(A, B) = (rk A + rk B) - (rk(A \/ B) + rk(A /\ B))
submodularDefect :: Lattice a => (a -> Integer) -> a -> a -> Integer
submodularDefect rk a b = (rk a + rk b) - (rk (a \/ b) + rk (a /\ b))

-- | Tor_0 in thin categories is the categorical meet
tor0 :: Lattice a => a -> a -> a
tor0 = (/\)

--------------------------------------------------------------------------------
-- 3. THE TRAVEL MONOID (N, +) x U2(Z) (§4)
--------------------------------------------------------------------------------

newtype Shear2D = Shear2D Integer deriving (Eq, Show)
instance Semigroup Shear2D where Shear2D a <> Shear2D b = Shear2D (a + b)
instance Monoid Shear2D    where mempty = Shear2D 0

-- | State space of Travel Experience Monoid: Trav = (N, +) x U2(Z)
data TravelExperience = TravelExperience
    { searchAction   :: !Word    -- ^ Accumulated search friction
    , shearTransport :: !Shear2D -- ^ Accumulated unipotent shear
    } deriving (Eq, Show)

instance Semigroup TravelExperience where
    TravelExperience s1 t1 <> TravelExperience s2 t2 = TravelExperience (s1 + s2) (t1 <> t2)

instance Monoid TravelExperience where
    mempty = TravelExperience 0 mempty

stepTravel :: Word -> Integer -> TravelExperience
stepTravel c s = TravelExperience c (Shear2D s)

--------------------------------------------------------------------------------
-- 4. CONNECTED LOEWY JOURNEY: LATTICE -> TRAVEL ODOMETER (Wire 1)
--------------------------------------------------------------------------------

-- | Covering step in the lattice: x <. y
covers :: (Poset a, Eq a) => [a] -> a -> a -> Bool
covers univ x y = (x <=: y) && (x /= y) &&
    not (any (\z -> z /= x && z /= y && (x <=: z) && (z <=: y)) univ)

-- | An actual covering step recorded with friction and shear data
data CoveringStep a = CoveringStep
    { stepFrom :: !a
    , stepTo   :: !a
    , stepCost :: !Word
    , stepExt  :: !Integer
    } deriving (Eq, Show)

-- | The completed Loewy Journey from Bottom to Top
data LoewyJourney a = LoewyJourney
    { journeyChain      :: ![a]              -- ^ Chain of subobjects x_0 <. x_1 <. ... <. x_n
    , journeySteps      :: ![CoveringStep a] -- ^ The elementary covering steps
    , journeyExperience :: !TravelExperience -- ^ Accumulated (Energy, Shear) along the path
    } deriving (Eq, Show)

-- | Greedily climbs the lattice from bottom to top, measuring path experience in real time
runLoewyJourney :: (BoundedLattice a, Eq a) => (a -> Maybe a) -> LoewyJourney a
runLoewyJourney findSimple = go bottom [] mempty
  where
    go curr accSteps accExp =
        case findSimple curr of
            Nothing -> LoewyJourney (reverse (curr : map stepFrom accSteps)) (reverse accSteps) accExp
            Just s  ->
                let nxt = curr \/ s
                in if nxt == curr
                   then LoewyJourney (reverse (curr : map stepFrom accSteps)) (reverse accSteps) accExp
                   else
                       let step = CoveringStep curr nxt 10 1  -- 10 cost units, 1 shear unit per step
                           newExp = accExp <> stepTravel (stepCost step) (stepExt step)
                       in go nxt (step : accSteps) newExp

--------------------------------------------------------------------------------
-- 5. THE CRYSTALLINE TOWER: CHAIN -> ASSOCIAHEDRON (Wire 2)
--------------------------------------------------------------------------------

-- | Binary trees representing parenthesizations of n-chains
data BinTree = Leaf | Fork !BinTree !BinTree deriving (Eq, Ord, Show)

leafCount :: BinTree -> Int
leafCount Leaf       = 1
leafCount (Fork l r) = leafCount l + leafCount r

-- | Catalan bracketings generator (C_{n-1} vertices)
allBracketings :: Int -> [BinTree]
allBracketings n
    | n <= 1    = [Leaf]
    | otherwise = [ Fork l r | k <- [1 .. n - 1], l <- allBracketings k, r <- allBracketings (n - k) ]

-- | Right rotations ((A * B) * C) -> (A * (B * C)) defining 1-skeleton edges
rightRotations :: BinTree -> [BinTree]
rightRotations Leaf = []
rightRotations (Fork l r) =
    rootRot ++ [Fork l' r | l' <- rightRotations l] ++ [Fork l r' | r' <- rightRotations r]
  where
    rootRot = case l of Fork a b -> [Fork a (Fork b r)]; Leaf -> []

-- | Dynamic Tamari order on binary trees for arbitrary n
tamariReachable :: BinTree -> BinTree -> Bool
tamariReachable from to
    | from == to = True
    | otherwise  = any (`tamariReachable` to) (rightRotations from)

instance Poset BinTree where
    (<=:) = tamariReachable

-- | Operadic boundary composition circ_i : K_r x K_s -> dK_{r+s-1}
graftAtLeaf :: Int -> BinTree -> BinTree -> BinTree
graftAtLeaf idx sub target = fst (go idx target)
  where
    go i Leaf       = if i == 0 then (sub, -1) else (Leaf, i - 1)
    go i (Fork l r) = let (l', i') = go i l
                      in if i' == -1 then (Fork l' r, -1) else let (r', i'') = go i' r in (Fork l' r', i'')

-- | Stasheff Associahedron K_n for an n-chain
data Associahedron = Associahedron
    { assocN        :: !Int
    , assocDim      :: !Int
    , assocVertices :: ![BinTree]
    , assocEdges    :: ![(BinTree, BinTree)]
    , assocFacets   :: !Int
    } deriving (Eq, Show)

buildAssociahedron :: Int -> Associahedron
buildAssociahedron n = Associahedron
    { assocN        = n
    , assocDim      = max 0 (n - 2)
    , assocVertices = vs
    , assocEdges    = [(u, v) | u <- vs, v <- rightRotations u]
    , assocFacets   = n * (n - 1) `div` 2 - 1
    }
  where vs = allBracketings n

crystallineTower :: [Associahedron]
crystallineTower = map buildAssociahedron [1 ..]

-- | Evaluates parenthesized compositions along the Loewy chain:
-- | In a thin category, all parenthesizations collapse to the unique arrow (diagram commutes).
evalChainParenthesization :: Poset a => [a] -> BinTree -> Maybe (ThinHom a a)
evalChainParenthesization chain _ =
    case (chain, reverse chain) of
        (start:_, end:_) -> thinHom start end
        _                -> Nothing

--------------------------------------------------------------------------------
-- 6. CARTAN METRIC & ROOT ENERGY: FACETS -> ROOTS (Wire 3)
--------------------------------------------------------------------------------

-- | Type A Cartan symmetric bilinear form <u, v>
cartanFormA :: [Integer] -> [Integer] -> Integer
cartanFormA u v = sum [ u' * v' * a_ij i j | (i, u') <- zip [1..] u, (j, v') <- zip [1..] v ]
  where
    a_ij i j | i == j           = 2
             | abs (i - j) == 1 = -1
             | otherwise        = 0

cartanSumOfSquares :: [Integer] -> Integer
cartanSumOfSquares []     = 0
cartanSumOfSquares [x]    = 2 * x^2
cartanSumOfSquares (x:xs) = x^2 + sum (zipWith (\a b -> (a - b)^2) (x:xs) xs) + last xs^2

-- | Almost-positive roots Φ_(≥-1)(A_d) for arbitrary dimension d
rootsA :: Int -> [[Integer]]
rootsA d = simplePositive ++ compoundPositive ++ negativeRoots
  where
    -- Simple positive roots: α_i
    simplePositive = [ [ if k == i then 1 else 0 | k <- [1..d] ] | i <- [1..d] ]
    -- Compound positive roots: α_i..j for i < j
    compoundPositive = [ [ if k >= i && k <= j then 1 else 0 | k <- [1..d] ] 
                       | i <- [1..d], j <- [i..d], i /= j ]
    -- Negative simple roots: -α_k
    negativeRoots = [ [ if k == i then -1 else 0 | k <- [1..d] ] | i <- [1..d] ]

-- | Direct mapping from Associahedron boundary facets to Root Vectors and their generalized Dirichlet-Cartan energy
facetRootEnergy :: Associahedron -> [([Integer], Integer)]
facetRootEnergy assoc =
    let d = max 1 (assocN assoc - 2) -- Dimension of the Lie algebra A_d
        roots = rootsA d
    in [ (r, cartanSumOfSquares r) | r <- roots ]


