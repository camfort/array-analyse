{-# LANGUAGE FlexibleInstances #-}

module Results where

import Control.Monad
import qualified Data.Map as M
import Data.List

import Camfort.Specification.Stencils.InferenceFrontend

-- Categories
data Kind = Read | Stencil deriving (Eq, Show, Ord)
data Contig = NonContig | Contig deriving (Eq, Show, Ord)


-- LHS assign, RHS subscript, RHS affine, RHS neigh
-- LHS subscript, RHS subscript, RHS affine, RHS neigh
-- LHS affine, RHS

-- lhs neight

data LHS = Assign | O Class
data Class = Subscript | Affine [(Int, String, Int)] | Neigh [Neighbour]


type Cat = (Kind, Contig)

isStencil (Stencil, _) = True
isStencil _            = False

isContig (_, Contig) = True
isContig _ = False

-- Results data type
data Result = Result {
    numLines                   :: Int   -- Number of lines parsed
  , numArrayWrites             :: Int   -- N  where N >= P + M
  , numIVArrayWrites           :: Int   -- P
  , numNeighbourArrayWrites    :: Int   -- M
  , numConstArrayWrites        :: Int   -- Q where M >= Q and M >= P
  , numLHSButNonNeighbourRHS   :: Int  -- Q1
  , numLHSButInconsistentIVRHS :: Int  -- Q2 where Q >= Q1 >= Q2
  ------------------------------------
  -- Special interest
  ------------------------------------
  , numSingNonContigStencils :: Int
  , numStencilRelativisedRHS :: Int
  ------------------------------------
  , numOverall  :: M.Map Cat Int
  , numLinear   :: M.Map Cat Int
  , numNoOrigin :: M.Map Cat Int
  ------------------------------------
  -- Histograms
  , histLengthOfDataflow :: M.Map Cat [Int]
  , histDimensionality   :: M.Map Cat [Int]
  , histMaxDepth         :: M.Map Cat [Int]
  , histNumArraysRead    :: M.Map Cat [Int]
  , histNumIndexExprs    :: M.Map Cat [Int]
  , histPatterns         :: M.Map Cat (M.Map Int Int
                                     , M.Map (Int, Int) Int
                                     , M.Map (Int, Int, Int) Int)

  } deriving Show


-- Results form a monoid
instance Monoid Result where
  mempty = Result 0 0 0  0 0 0 0
                  0 0
                  (catMapEmpty 0) (catMapEmpty 0) (catMapEmpty 0)
                  (catMapEmpty []) (catMapEmpty []) (catMapEmpty [])
                  (catMapEmpty []) (catMapEmpty [])
                  (catMapEmpty (M.empty, M.empty, M.empty))

    where catMapEmpty e = M.fromList [((Stencil, Contig), e), ((Stencil, NonContig), e),
                                     ((Read, Contig), e), ((Read, NonContig), e)]

  mappend r1 r2 = Result
     { numLines = numLines r1 + numLines r2
     , numArrayWrites = numArrayWrites r1 + numArrayWrites r2
     , numIVArrayWrites = numIVArrayWrites r1 + numIVArrayWrites r2
     , numNeighbourArrayWrites = numNeighbourArrayWrites r1
                                + numNeighbourArrayWrites r2

     , numConstArrayWrites = numConstArrayWrites r1
                               + numConstArrayWrites r2

     , numLHSButNonNeighbourRHS = numLHSButNonNeighbourRHS r1
                                 + numLHSButNonNeighbourRHS r2

     , numLHSButInconsistentIVRHS = numLHSButInconsistentIVRHS r1
                                  + numLHSButInconsistentIVRHS r2

     , numStencilRelativisedRHS = numStencilRelativisedRHS r1
                                + numStencilRelativisedRHS r2

     , numSingNonContigStencils = numSingNonContigStencils r1
                                + numSingNonContigStencils r2

     , numOverall = M.unionWith (+) (numOverall r1) (numOverall r2)
     , numLinear  = M.unionWith (+) (numLinear r1) (numLinear r2)
     , numNoOrigin = M.unionWith (+) (numNoOrigin r1) (numNoOrigin r2)
     , histLengthOfDataflow = M.unionWith histZip (histLengthOfDataflow r1) (histLengthOfDataflow r2)
     , histDimensionality = M.unionWith histZip (histDimensionality r1) (histDimensionality r2)
     , histMaxDepth = M.unionWith histZip (histMaxDepth r1) (histMaxDepth r2)
     , histNumArraysRead = M.unionWith histZip (histNumArraysRead r1) (histNumArraysRead r2)
     , histNumIndexExprs = M.unionWith histZip (histNumIndexExprs r1) (histNumIndexExprs r2)
     , histPatterns = M.unionWith histZip (histPatterns r1) (histPatterns r2)
     }

-- Operations for combining different kinds of histograms
class HistogramZip t where
    histZip :: t -> t -> t

instance HistogramZip [Int] where
    histZip [] xs = xs
    histZip xs [] = xs
    histZip (x:xs) (y:ys) = (x+y):(histZip xs ys)

instance HistogramZip a => HistogramZip (a, a) where
    histZip (a, b) (x, y) = (histZip a x, histZip b y)

instance (HistogramZip a, HistogramZip b, HistogramZip c) => HistogramZip (a, b, c) where
    histZip (a, b, c) (x, y, z) = (histZip a x, histZip b y, histZip c z)

instance Ord k => HistogramZip (M.Map k Int) where
    histZip x y = M.unionWith (+) x y

--------------------------------------------------------------------------------
-- Pretty print results
--------------------------------------------------------------------------------

prettyResults r histograms =
    "Results: \n"
 ++ rline "Source lines parsed" (numLines r)
 ++ rline "Array writes" (numArrayWrites r)
 ++ rline "Array writes to neighbourhood indices"
          (numNeighbourArrayWrites r - numConstArrayWrites r)
 ++ rline "Array writes to I.V. indices" (numIVArrayWrites r)
 ++ rline "Array writes to neighbourhood+constant IV indices" (numConstArrayWrites r)
 ++ rline "Neighbour LHS but RHS with non-neighbour indices" (numLHSButNonNeighbourRHS r)
 ++ rline "Neighbour LHS but RHS with inconsistent IV use" (numLHSButInconsistentIVRHS r)
 ++ "----------------------------------------------------------------------------\n"
 ++ "Categorisations: \n"
 ++ showCats "Number of" (numOverall r)
 ++ showCats "Number of linear" (numLinear r)
 ++ showCats "Number with no origin" (numNoOrigin r)
 ++ rline "Non-contiguous stencils with one index" (numSingNonContigStencils r)
 ++ "----------------------------------------------------------------------------\n"
 ++ if histograms then
       "Histograms and median: \n"
        ++ hline "Dimensionality" (histDimensionality r)
        ++ hline "Maximum depth" (histMaxDepth r)
        ++ hline "Arrays read in stencil" (histNumArraysRead r)
        ++ hline "Indexing terms in stencil" (histNumIndexExprs r)
        ++ hline "Length of (array read) dataflow path" (histLengthOfDataflow r)
        ++ rline' "Indexing pattern heat map" (histPatterns r)
        ++ "\n"
    else ""

rline msg num = "   " ++ msg ++ ":" ++ (replicate (60 - (length msg)) ' ') ++ (show num) ++ "\n"
rline' msg num = "   " ++ msg ++ ":" ++ (replicate (60 - (length msg)) ' ') ++ "\n" ++ (show num) ++ "\n"
hline msg map =
     hline' msg "Stencils" Stencil map
  ++ hline' msg "Reads" Read map

hline' msg msg' cat map =
  "   " ++ msg ++ "\n"
  ++ "    " ++ msg' ++ ":\n"
  ++ "      Continguous:\n" ++ hview contigHist ++ "\n"
  ++ "      Non-contig.:\n" ++ hview noncontigHist ++ "\n"
  ++ "      Total:\n" ++ hview (histZip contigHist noncontigHist) ++ "\n"
  where
    contigHist = map M.! (cat, Contig)
    noncontigHist = map M.! (cat, NonContig)

hview :: [Int] -> String
hview xs = "         k: " ++ top ++ "\n" ++ "         v: " ++ bottom
  where
    (top, bottom) = hview' (zip [0..(length xs)] xs) False
    hview' :: [(Int, Int)] -> Bool -> (String, String)
    hview' [] _ = ("", "")
    hview' [(n, x)] _ = (show n, show x)
    hview' ((l, 0):rest) True = hview' rest True
    hview' ((l, 0):(m, 0):(n, 0):rest) False = ("... ", "... ") `mappend` hview' rest True
    hview' ((n, x):rest) _ = (pad n ++ " | ", pad x ++ " | ") `mappend` hview' rest False
      where width = (length . show $ n) `max` (length . show $ x)
            pad :: Int -> String
            pad x = (show x) ++ (replicate (width - (length . show $ x)) ' ')

showCats :: (Num a, Show a) => String -> M.Map Cat a -> String
showCats prefix amap =
     showCat Stencil " stencils"
  ++ showCat Read " reads"
  where
    showCat cat msg =
      let prefix' = prefix ++ msg
      in rline prefix' (amap M.! (cat, Contig) + amap M.! (cat, NonContig))
      ++ (rline ((replicate 46 ' ') ++ "(contiguous)") $ amap M.! (cat, Contig))
      ++ (rline ((replicate 42 ' ') ++ "(non-contiguous)") $ amap M.! (cat, NonContig))
      ++ "\n"

--------------------------------------------------------------------------------
-- Validate results
--------------------------------------------------------------------------------

resultValidation =
      (\r -> (numArrayWrites r) `gte` (numNeighbourArrayWrites r))
          `reason` "Array writes >= Neighbour Writes"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` ((numIVArrayWrites r) + (numConstArrayWrites r)))
          `reason` "Neighour Writes >= (IV Writes + Neigh/Const Writes)"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` (numLHSButNonNeighbourRHS r))
          `reason` "Neighbour Writes >= Non-neighour RHS"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` (numLHSButInconsistentIVRHS r))
          `reason` "Neighbour Writes >= Inconsistent IV RHS"

 <**> (\r -> ((sumMap . justStencils $ (numOverall r))
               + (numLHSButInconsistentIVRHS r) + (numLHSButNonNeighbourRHS r))
           `eq` (numNeighbourArrayWrites r))
          `reason` "Num stencils + RHS inconsistent IV + RHS non-neighbour = LHS Neighbour"

 <**> (\r -> (numStencilRelativisedRHS r)
          `eq` ((numNeighbourArrayWrites r) - ((numConstArrayWrites r) + (numIVArrayWrites r))))
          `reason` "Num relativised stencils = LHS Neighbour with some relative offset"

 <**> (\r -> (sumMap . justStencils $ (numOverall r))
            `gte` ((sumMap . justContigStencils $ (numOverall r)) + (numSingNonContigStencils r)))
           `reason` "Num stencils >= Num contiguous stencils + num non-contig single index"
 where sumMap = Data.List.sum . M.elems
       justStencils = fst . M.partitionWithKey (\k _ -> isStencil k)
       justContigStencils = fst . M.partitionWithKey (\k _ -> isStencil k && isContig k)

gte, eq :: Int -> Int -> (Bool, Int, Int)
gte x y = (x >= y, x, y)
eq x y  = (x == y, x, y)

reason :: (Result -> (Bool, Int, Int)) -> String -> (Result -> IO Bool)
reason f reason = \r -> do
     let (validity, x, y) = f r
     when (not validity) (putStrLn $ reason ++ ": " ++ (show validity) ++ " - " ++ show x ++ ", " ++ show y)
     return validity

infixr 5 <**>
(<**>) :: (Result -> IO Bool) -> (Result -> IO Bool) -> (Result -> IO Bool)
f <**> g = \r -> (f r) >>= (\x -> g r >>= (\y -> return (x && y)))
