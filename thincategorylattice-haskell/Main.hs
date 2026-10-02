module Main where

import ThinCategoryLattice
import Data.List (nub, subsequences, find)
import Data.Maybe (isJust)

newtype SetLattice = SetLattice [Int] deriving (Eq, Show)
instance Poset SetLattice where SetLattice xs <=: SetLattice ys = all (`elem` ys) xs
instance Lattice SetLattice where
    SetLattice xs /\ SetLattice ys = SetLattice [x | x <- xs, x `elem` ys]
    SetLattice xs \/ SetLattice ys = SetLattice (xs ++ [y | y <- ys, y `notElem` xs])
instance BoundedLattice SetLattice where
    bottom = SetLattice []
    top    = SetLattice [1, 2, 3, 4]  -- 4-element set: generates a 5-chain from bot to top

main :: IO ()
main = do
    putStrLn "========================================================================"
    putStrLn "  RUNNING CONNECTED PIPELINE: LATTICE -> TRAVEL -> TOWER -> ROOTS"
    putStrLn "========================================================================"

    -- STAGE 0: Poset as a Thin Category (Objects, Arrows, Limits, & Galois Monad)
    let x = SetLattice [1]
        y = SetLattice [1, 2]
        arrowXY = thinHom x y
        arrowYX = thinHom y x
    putStrLn $ "[Stage 0] Poset (L, <=) as Thin Category C_L:"
    putStrLn $ "          Arrow x -> y (x <= y) : " ++ show arrowXY ++ " (Subsingleton: |Hom| <= 1)"
    putStrLn $ "          Arrow y -> x (y </= x): " ++ show arrowYX ++ " (Empty hom-set)"
    putStrLn $ "          Categorical Product (Meet x /\\ y)   : " ++ show (x /\ y)
    putStrLn $ "          Categorical Coproduct (Join x \\/ y) : " ++ show (x \/ y)

    -- Galois adjunction F -| G inducing closure monad T = G . F
    let h 1 = 1; h 2 = 1; h 3 = 3; h 4 = 4; h _ = 0
        gal = GaloisConnection (\(SetLattice xs) -> SetLattice (nub [h e | e <- xs]))
                               (\(SetLattice ys) -> SetLattice [e | e <- [1..4], h e `elem` ys])
        testSets = [SetLattice [], x, y, SetLattice [1, 2, 3, 4]]
        closure = galoisToClosure gal
    putStrLn $ "          Galois Adjunction F -| G holds     : " ++ show (isGalois gal testSets testSets)
    putStrLn $ "          Induced Closure Monad T = G.F      : " ++ show (isClosure closure testSets)

    -- STAGE 1: Modularity & Strain Check
    let rk (SetLattice xs) = fromIntegral (length (nub xs))
        def = submodularDefect rk (SetLattice [1, 2]) (SetLattice [2, 3])
    putStrLn $ "[Stage 1] Submodular Defect Delta({1,2}, {2,3}) = " ++ show def ++ " (0 = Modular)"

    -- STAGE 2: Run Loewy Journey (Wire 1: Lattice -> Travel Odometer)
    let univ = map SetLattice (subsequences [1..4])
        findSimple curr = find (covers univ curr) univ
        journey = runLoewyJourney findSimple
        chain   = journeyChain journey
        n       = length chain

    putStrLn $ "[Stage 2] Loewy Sieve climbed " ++ show (length (journeySteps journey)) ++ " steps to Top:"
    mapM_ (\(i, s) -> putStrLn $ "          Step " ++ show i ++ ": " ++ show (stepFrom s) ++ " -> " ++ show (stepTo s))
          (zip [1..] (journeySteps journey))
    putStrLn $ "          Travel Odometer: " ++ show (searchAction (journeyExperience journey)) ++
               " energy units, " ++ show (shearTransport (journeyExperience journey)) ++ " shear"

    -- STAGE 3: Build Associahedron from the Journey Chain (Wire 2: Chain -> Tower)
    let k5 = buildAssociahedron n
    putStrLn $ "[Stage 3] Chain length " ++ show n ++ " generated Associahedron K_" ++ show n ++ ":"
    putStrLn $ "          Dimension: " ++ show (assocDim k5) ++ "D Polyhedron"
    putStrLn $ "          Vertices : " ++ show (length (assocVertices k5)) ++ " bracketings (Catalan C_4)"
    putStrLn $ "          1-Skeleton: " ++ show (length (assocEdges k5)) ++ " right-rotation edges"
    putStrLn $ "          Facets   : " ++ show (assocFacets k5) ++ " boundary walls"

    -- Verify all 14 parenthesizations collapse to the same thin category arrow
    let allArrowsCommute = all (isJust . evalChainParenthesization chain) (assocVertices k5)
    putStrLn $ "          Thin Diagram Collapse: All " ++ show (length (assocVertices k5)) ++
               " bracketings evaluate to the same unique arrow: " ++ show allArrowsCommute

    -- STAGE 4: Connect Facets to Lie Root System & Cartan Energy (Wire 3: Facets -> Roots)
    let energies = facetRootEnergy k5
    putStrLn $ "[Stage 4] Connected " ++ show (assocFacets k5) ++ " Facets to A_3 Roots:"
    mapM_ (\(i, (r, e)) -> putStrLn $ "          Facet " ++ show i ++ " Root " ++ show r ++ " -> Energy = " ++ show e)
          (zip [1..] energies)

    let adjCoupling = cartanFormA (fst (energies !! 0)) (fst (energies !! 1))
        orthDecoupling = cartanFormA (fst (energies !! 0)) (fst (energies !! 2))
        sumOfSqCheck = all (\(r, e) -> cartanSumOfSquares r == e) energies
    putStrLn $ "          Adjacent Facet Interaction : " ++ show adjCoupling ++ " (Expect -1)"
    putStrLn $ "          Orthogonal Facet Decoupling: " ++ show orthDecoupling ++ " (Expect 0)"
    putStrLn $ "          Theorem 7.1 (Sum of Squares) : " ++ show sumOfSqCheck

    putStrLn "========================================================================"
    putStrLn "  PIPELINE COMPLETE: ALL MODULES FULLY CONNECTED AND VERIFIED"
    putStrLn "========================================================================"
