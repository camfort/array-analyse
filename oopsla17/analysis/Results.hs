{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs, DataKinds, PolyKinds, KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Results where

import Control.Monad
import qualified Data.Map as M
import Data.List

import Camfort.Specification.Stencils.InferenceFrontend
import Camfort.Specification.Stencils.Syntax (absoluteRep)

-- ## Categorisations:

--   * RHS shape/position/contiguity
data Shape    = Orthotope | SumOfOrthotope | Other
              -- I think 'Other' shouldn't actually occur, but until I have a proof
              -- I'll leave this hear to catch 'unwiedly' things
    deriving (Eq, Show, Ord, Read)

data Position = OverOrigin | StraddleOrigin | Elsewhere
    deriving (Eq, Show, Ord, Read)

joinPosition :: Position -> Position -> Position
joinPosition OverOrigin OverOrigin = OverOrigin
joinPosition StraddleOrigin StraddleOrigin = StraddleOrigin
joinPosition _ _ = Elsewhere

data Contig   = SingleNonContig | NonContig | Contig
    deriving (Eq, Show, Ord, Read)

boolToContig :: Bool -> Contig
boolToContig True = Contig
boolToContig False = NonContig

data Reuse    = Linear | NonLinear
    deriving (Eq, Show, Ord, Read)

boolToReuse :: Bool -> Reuse
boolToReuse True = Linear
boolToReuse False = NonLinear

data Physicality s where
     L :: Physicality LHS
     R :: (Shape, Position, Contig, Reuse) -> Physicality RHS

deriving instance Eq (Physicality s)
deriving instance Ord (Physicality s)
deriving instance Show (Physicality s)

instance Read (Physicality LHS) where
  readsPrec n ('L':xs) = [(L, xs)]
  readsPrec n _        = []

instance Read (Physicality RHS) where
  readsPrec n ('R':' ':xs) = map (\(n, rest) -> (R n, rest)) $ readsPrec n xs
  readsPrec n _            = []

--   * Categorisation of indices (on LHS or RHS)
data Side = LHS | RHS

data HasConstants = WithConsts | Normal
   deriving (Eq, Ord)

instance Show HasConstants where
   show WithConsts = "+consts"
   show Normal     = ""

instance Read HasConstants where
   readsPrec n xs | "+consts" `isPrefixOf` xs
       = [(WithConsts, drop (length "+consts") xs)]
                  | otherwise = [(Normal, trim xs)]

boolToHasConstants :: Bool -> HasConstants
boolToHasConstants True = WithConsts
boolToHasConstants False = Normal

data Form (s :: Side) where
    Vars        :: Form LHS
    Subscripts  :: Form s
    Affines     :: HasConstants -> Physicality s -> Form s
    Neighbours  :: HasConstants -> Physicality s -> Form s
    IVs         :: Form LHS

deriving instance Eq (Form s)
deriving instance Ord (Form s)
deriving instance Show (Form s)

instance Read (Form LHS) where
  readsPrec n xs | "Vars" `isPrefixOf` xs
    = [(Vars, drop (length "Vars") xs)]
  readsPrec n xs | "Subscripts" `isPrefixOf` xs
    = [(Subscripts, drop (length "Subscripts") xs)]

  readsPrec n xs | "Affines" `isPrefixOf` xs
    = do (consts, rest) <- readsPrec n (drop (length "Affines ") xs)
         (pl, rest)     <- readsPrec n rest
         return (Affines consts pl, rest)

  readsPrec n xs | "Neighbours" `isPrefixOf` xs
    = do (consts, rest) <- readsPrec n (drop (length "Neighbours ") xs)
         (pl, rest)     <- readsPrec n rest
         return (Neighbours consts pl, rest)

  readsPrec n xs | "IVs" `isPrefixOf` xs
    = [(IVs, drop (length "IVs") xs)]

  readsPrec n xs = []

instance Read (Form RHS) where
  readsPrec n xs | "Subscripts" `isPrefixOf` xs
    = [(Subscripts, drop (length "Subscripts") xs)]

  readsPrec n xs | "Affines" `isPrefixOf` xs
    = do (consts, '(':rest) <- readsPrec n (drop (length "Affines ") xs)
         (pr, ')':rest)     <- readsPrec n rest
         return (Affines consts pr, rest)

  readsPrec n xs | "Neighbours" `isPrefixOf` xs
    = do (consts, '(':rest) <- readsPrec n (drop (length "Neighbours ") xs)
         (pr, ')':rest)     <- readsPrec n rest
         return (Neighbours consts pr, rest)

  readsPrec n xs = []

type Relativised = Bool

--   * Consistency between sides
data Consistency = Consistent  Relativised
                 | Permutation Relativised
                 | LHSsubset   Relativised
                 | LHSsuperset Relativised
                 | Inconsistent
      deriving (Eq, Ord)

instance Read Consistency where
  readsPrec n xs =
       consistencyRead "Consistent"  Consistent 0 xs
    ++ consistencyRead "Permutation" Permutation 0 xs
    ++ consistencyRead "LHSsubset"   LHSsubset 0 xs
    ++ consistencyRead "LHSsuperset" LHSsuperset 0 xs
    ++ consistencyRead "Inconsitent" (\b -> Inconsistent) 0 xs

consistencyRead consString cons n xs =
    if consString `isPrefixOf` xs
    then [(cons relFlag, drop (length (consString ++ showR relFlag)) xs)]
    else []
  where
    relFlag = (showR True) `isPrefixOf` (drop (length consString) xs)

readR xs = (showR True) `isSuffixOf` xs

instance Show Consistency where
  show (Consistent r)  = "Consistent" ++ showR r
  show (Permutation r) = "Permutation" ++ showR r
  show (LHSsubset r)   = "LHSsubset" ++ showR r
  show (LHSsuperset r) = "LHSsuperset" ++ showR r
  show Inconsistent    = "Inconsistent"

showR True = " relativised"
showR False = ""

setRelativised :: Consistency -> Bool -> Consistency
setRelativised (Consistent _)  r = Consistent r
setRelativised (Permutation _) r = Permutation r
setRelativised (LHSsubset   _) r = LHSsubset r
setRelativised (LHSsuperset _) r = LHSsuperset r
setRelativised Inconsistent    _ = Inconsistent

joinConsistency :: Consistency -> Consistency -> Consistency
joinConsistency (Consistent r)  (Consistent s)  = Consistent (r && s)
joinConsistency (Permutation r) (Permutation s) = Permutation (r && s)
joinConsistency (LHSsubset r)   (LHSsubset s)   = LHSsubset (r && s)
joinConsistency (LHSsuperset r) (LHSsuperset s) = LHSsuperset (r && s)
joinConsistency Inconsistent    Inconsistent    = Inconsistent
joinConsistency _               _               = Inconsistent

-- Overall categorisation
type Cat = (Form LHS, Form RHS, Consistency)

-- Results data type
data Result = Result {
    numLines              :: Int
  , counts                :: M.Map Cat Int
  ------------------------------------
  -- Histograms
  , histDimensionality   :: M.Map Cat [Int]
  , histMaxDepth         :: M.Map Cat [Int]
  , histNumIndexExprs    :: M.Map Cat [Int]
  , histNumArraysRead    :: [Int]
  , histLengthOfDataflow :: [Int]
  , histAffineScale      :: [Int]
  , patternBin1D         :: M.Map [Int] Int
  , patternBin2D         :: M.Map [(Int,Int)] Int
  , patternBin3D         :: M.Map [(Int, Int, Int)] Int
  } deriving (Show, Read)

-- pre-condition: list of 1-dimensional offsets
to1D :: [[Int]] -> [Int]
to1D [] = []
to1D ([x]:xs) = x : to1D xs
-- pre-condition: list of 2-dimensional offsets
to2D :: [[Int]] -> [(Int, Int)]
to2D [] = []
to2D ([x, y]:xs) = (x, y) : to2D xs
-- pre-condition: list of 3-dimensional offsets
to3D :: [[Int]] -> [(Int, Int, Int)]
to3D [] = []
to3D ([x, y, z]:xs) = (x, y, z) : to3D xs
-- Indicates a bug in the analysed code
to3D ([x, y]:xs)    = (x, y, absoluteRep) : to3D xs
to3D ([x]:xs)       = (x, absoluteRep, absoluteRep) : to3D xs


-- Results form a monoid
instance Monoid Result where
  mempty = Result 0 M.empty M.empty M.empty M.empty [] [] [] M.empty M.empty M.empty

  mappend r1 r2 = Result
     { numLines = numLines r1 + numLines r2
     , counts = M.unionWith (+) (counts r1) (counts r2)

     , histDimensionality = M.unionWith histZip (histDimensionality r1)
                                                (histDimensionality r2)
     , histMaxDepth = M.unionWith histZip (histMaxDepth r1) (histMaxDepth r2)
     , histNumIndexExprs = M.unionWith histZip (histNumIndexExprs r1)
                                               (histNumIndexExprs r2)

     , histNumArraysRead = histZip (histNumArraysRead r1) (histNumArraysRead r2)
     , histLengthOfDataflow = histZip (histLengthOfDataflow r1) (histLengthOfDataflow r2)
     , histAffineScale = histZip (histAffineScale r1) (histAffineScale r2)
     , patternBin1D = M.unionWith (+) (patternBin1D r1) (patternBin1D r2)
     , patternBin2D = M.unionWith (+) (patternBin2D r1) (patternBin2D r2)
     , patternBin3D = M.unionWith (+) (patternBin3D r1) (patternBin3D r2)
     }

-- Combine histograms
histZip :: [Int] -> [Int] -> [Int]
histZip [] xs = xs
histZip xs [] = xs
histZip (x:xs) (y:ys) = (x+y):(histZip xs ys)

-- Histogram manipulation
flag True = 1
flag False = 0

-- Generate a singleton histogram for value 'n'
toHist :: Int -> [Int]
toHist n = (replicate n 0) ++ [1]

-- 'zip' together a list of histograms
concatHist :: [[Int]] -> [Int]
concatHist = foldr histZip []

-- Singleton histogram
mkHist :: Cat -> a -> M.Map Cat a
mkHist cat x = M.fromList [(cat, x)]


--------------------------------------------------------------------------------
-- Pretty print results
--------------------------------------------------------------------------------

prettyResults r bins =
    "Results: \n"
 ++ rline "Source lines parsed" (numLines r)
 ++ mapView "Counts" (counts r)
 ++ mapView "Dimensionality" (histDimensionality r)
 ++ mapView "Max depth" (histMaxDepth r)
 ++ mapView "Number of indexing expressions" (histNumIndexExprs r)
 ++ rline' "Number of arrays read"    (hview . histNumArraysRead $ r)
 ++ rline' "Length of dataflow path"  (hview . histLengthOfDataflow $ r)
 ++ rline' "Scale of affine indexing" (hview . histAffineScale $ r)
 ++ if bins
    then binView "1D patterns" (patternBin1D r)
      ++ binView "2D patterns" (patternBin2D r)
      ++ binView "3D patterns" (patternBin3D r)
    else ""
rline msg num = "   " ++ msg ++ ":" ++ (replicate (90 - (length msg)) ' ') ++ (show num) ++ "\n"
rline' msg dat = "   " ++ msg ++ ":" ++ (replicate (90 - (length msg)) ' ') ++ dat ++ "\n"

binView msg bin =
      rline msg (length . M.keys $ bin)
   ++ (concatMap (\(pat, count) -> "      " ++ show count ++ " of " ++ show pat ++ "\n")
        (M.assocs bin))

mapView msg map =
       "   " ++ msg ++ ":\n"
    ++ rline' ((replicate 5 ' ') ++ "Total") (show' . histTotal $ M.elems map)
    ++ concatMap (\(cat, dat) -> hline' cat (show' dat)) (M.assocs map)
    ++ "\n"

class HistogramShow t where
  show'     :: t -> String
  histTotal :: [t] -> t

instance HistogramShow Int where
  show'     = show
  histTotal = sum

instance HistogramShow [Int] where
  show'     = hview
  histTotal = foldr histZip []

hline' cat dat =
  rline' ((replicate 5 ' ') ++ (show cat)) dat

hview :: [Int] -> String
hview xs = "k: "
        ++ top ++ "\n"
        ++ (replicate 94 ' ')
        ++ "v: "
        ++ bottom
        ++ "\n"
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

--------------------------------------------------------------------------------
-- Validate results
--------------------------------------------------------------------------------

resultValidation :: Result -> IO Bool
resultValidation r = return True --  TO-REDO

{-
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
-}

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

trim (' ':xs) = trim xs
trim xs = xs