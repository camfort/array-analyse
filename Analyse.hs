{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Main where

import Camfort.Analysis.Simple
import Camfort.Functionality
import Camfort.Input

import Control.Exception
import Control.Monad
import Data.List
import Data.Monoid
import Data.Typeable
import System.Environment
import System.Directory

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Product)

import Camfort.Analysis.CommentAnnotator

import Camfort.Specification.Stencils.InferenceBackend
import Camfort.Specification.Stencils.InferenceFrontend
import Camfort.Specification.Stencils.Syntax
import Camfort.Specification.Stencils.Annotation
import qualified Camfort.Specification.Stencils.Grammar as Gram
import qualified Camfort.Specification.Stencils.Synthesis as Synth
import Camfort.Analysis.Annotations
import Camfort.Helpers.Vec
import Camfort.Helpers (Filename, SourceText, collect)
import Camfort.Input
import qualified Camfort.Output as O

import qualified Language.Fortran.AST as F
import qualified Language.Fortran.Analysis as FA
import qualified Language.Fortran.Analysis.Types as FAT
import qualified Language.Fortran.Analysis.Renaming as FAR
import qualified Language.Fortran.Analysis.BBlocks as FAB
import qualified Language.Fortran.Analysis.DataFlow as FAD
import qualified Language.Fortran.Util.Position as FU
import qualified Language.Fortran.Util.SecondParameter as FUS

import Data.Data
import Data.Foldable
import Data.Generics.Uniplate.Operations
import Data.Graph.Inductive.Graph hiding (isEmpty)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.ByteString.Char8 as B
import Data.Maybe
import Data.List
import Data.Monoid
import Debug.Trace

main :: IO ()
main = do
    args <- getArgs
    if (length args == 1) then
      applyAnalysisToDir (head args) False []
    else if (length args > 1) then
      if (args !! 1 == "-d") then
         applyAnalysisToDir (head args) True (tail (tail args))
      else
         applyAnalysisToDir (head args) False (tail args)
    else
      putStrLn $ "Please specify a directory on which to apply the analysis\
                 \ followed by any number of file names to be excluded "

applyAnalysisToDir :: String -> Bool -> [String] -> IO ()
applyAnalysisToDir dir debug excludes = do
    files <- readParseSrcDir dir excludes
    let debugsAndResults = map applyAnalysisToFile files
    let (dbg, result)   = mconcat debugsAndResults
    if debug then putStrLn $ dbg else return ()
    putStrLn $ prettyResults result
    valid <- resultValidation result
    if valid then (putStrLn $ "Results were valid") else (putStrLn "Results were invalid")

type ForContigAndNonContig a = (a, a)

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
  , numStencils                :: Int   -- b
  , numRelativisedRHS          :: Int   -- R (where R = M)
  , numContiguousStencils      :: Int    -- c  where p >= c
  , numNoOrigin                :: Int    -- c' where c >= c'
  , numSingNonContigStencils   :: Int
  , numContigLinearStencils    :: Int    -- d  where c >= d
  , dimensionalityHist         :: ForContigAndNonContig [Int]
                                 -- (h1, h1n) where sum(h1) == c
  , maxDepthHist               :: ForContigAndNonContig [Int]
                                 -- (h2, h2n) where sum(h2) == c
  , numArraysReadHist          :: ForContigAndNonContig [Int]
  , numIndexExprsHist          :: ForContigAndNonContig [Int]
                                 -- h3
  , patternHist                :: ForContigAndNonContig
                              (M.Map Int Int
                             , M.Map (Int, Int) Int
                             , M.Map (Int, Int, Int) Int)
                            -- only for 1, 2 and 3 dimensional specs
    } deriving Show

resultValidation =
      (\r -> (numArrayWrites r) `gte` (numNeighbourArrayWrites r))
          `reason` "Array writes >= Neighbour Writes"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` ((numIVArrayWrites r) + (numConstArrayWrites r)))
          `reason` "Neighour Writes >= (IV Writes + Neigh/Const Writes)"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` (numLHSButNonNeighbourRHS r))
          `reason` "Neighbour Writes >= Non-neighour RHS"

 <**> (\r -> (numNeighbourArrayWrites r) `gte` (numLHSButInconsistentIVRHS r))
          `reason` "Neighbour Writes >= Inconsistent IV RHS"

 <**> (\r -> ((numStencils r) + (numLHSButInconsistentIVRHS r) + (numLHSButNonNeighbourRHS r))
           `eq` (numNeighbourArrayWrites r))
          `reason` "Num stencils + RHS inconsistent IV + RHS non-neighbour = LHS Neighbour"

 <**> (\r -> (numRelativisedRHS r)
          `eq` ((numNeighbourArrayWrites r) - ((numConstArrayWrites r) + (numIVArrayWrites r))))
          `reason` "Num relativised stencils = LHS Neighbour with some relative offset"

 <**> (\r -> (numStencils r)
            `gte` ((numContiguousStencils r) + (numSingNonContigStencils r)))
           `reason` "Num stencils >= Num contiguous stencils + num non-contig single index"

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

prettyResults r =
    "Results: \n"
 ++ rline "Source lines parsed" (numLines r)
 ++ rline "Array writes" (numArrayWrites r)
 ++ rline "Array writes to neighbourhood indices"
          (numNeighbourArrayWrites r - numConstArrayWrites r)
 ++ rline "Array writes to I.V. indices" (numIVArrayWrites r)
 ++ rline "Array writes to neighbourhood+constant IV indices" (numConstArrayWrites r)
 ++ rline "Neighbour LHS but RHS with non-neighbour indices" (numLHSButNonNeighbourRHS r)
 ++ rline "Neighbour LHS but RHS with inconsistent IV use" (numLHSButInconsistentIVRHS r)
 ++ rline "Stencils" (numStencils r)
 ++ rline "Relativised stencils" (numRelativisedRHS r)
 ++ rline "Contiguous stencils (including no origin)" (numContiguousStencils r)
 ++ rline "Stencils with no origin" (numNoOrigin r)
 ++ rline "Non-contiguous stencils with one index" (numSingNonContigStencils r)
 ++ rline "Contiguous linear stencils" (numContigLinearStencils r)
 ++ "----------------------------------------------------------------------------\n"
 ++ "Histograms and median: \n"
 ++ hline "Dimensionality" (dimensionalityHist r)
 ++ hline "Maximum depth" (maxDepthHist r)
 ++ hline "Arrays read in stencil" (numArraysReadHist r)
 ++ hline "Indexing terms in stencil" (numIndexExprsHist r)
 ++ rline' "Indexing pattern heat map" (patternHist r)
 ++ "\n"

rline msg num = "   " ++ msg ++ ":" ++ (replicate (60 - (length msg)) ' ') ++ (show num) ++ "\n"
rline' msg num = "   " ++ msg ++ ":" ++ (replicate (60 - (length msg)) ' ') ++ "\n" ++ (show num) ++ "\n"
hline msg (contigHist, noncontigHist) =
  "   " ++ msg ++ "\n"
  ++ "      Continguous stencils:\n" ++ hview contigHist ++ "\n"
  ++ "      Non-contig. stencils:\n" ++ hview noncontigHist ++ "\n"
  ++ "      Total:\n" ++ hview (histZip contigHist noncontigHist) ++ "\n"

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

-- Results form a monoid
instance Monoid Result where
  mempty = Result 0 0 0 0 0 0 0 0 0 0 0 0 0 ([],[]) ([],[]) ([],[]) ([],[])
            ((M.empty, M.empty, M.empty), (M.empty, M.empty, M.empty))

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

     , numStencils = numStencils r1 + numStencils r2

     , numRelativisedRHS = numRelativisedRHS r1
                         + numRelativisedRHS r2

     , numContiguousStencils = numContiguousStencils r1
                             + numContiguousStencils r2

     , numNoOrigin = numNoOrigin r1 + numNoOrigin r2

     , numSingNonContigStencils = numSingNonContigStencils r1 + numSingNonContigStencils r2

     , numContigLinearStencils = numContigLinearStencils r1 + numContigLinearStencils r2

     , dimensionalityHist = histZip (dimensionalityHist r1) (dimensionalityHist r2)
     , maxDepthHist = histZip (maxDepthHist r1) (maxDepthHist r2)
     , numArraysReadHist = histZip (numArraysReadHist r1) (numArraysReadHist r2)
     , numIndexExprsHist = histZip (numIndexExprsHist r1) (numIndexExprsHist r2)
     , patternHist = histZip (patternHist r1) (patternHist r2)
     }

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

applyAnalysisToFile :: (Filename, SourceText, F.ProgramFile A) -> (String, Result)
applyAnalysisToFile (filename, source, pf) =
    ("Analysis on file: " ++ filename ++ "\n" ++ dbg, r { numLines = lines })
  where
    lines = length $ B.lines source
    pf' = FAR.analyseRenames . FA.initAnalysis $ pf
    nameMap = FAR.extractNameMap pf'
    (dbg, r) = stencilAnalyse nameMap . FAB.analyseBBlocks $ pf'

-- The core of the analysis works within this monad
type Analysis = WriterT (String, Result)
                 (ReaderT (FAD.FlowsGraph A, FAR.NameMap)
                    (State FAD.InductionVarMapByASTBlock))

runAnalysis :: FAD.InductionVarMapByASTBlock
            -> FAD.FlowsGraph A
            -> FAR.NameMap
            -> Analysis a
            -> (a, (String, Result))
runAnalysis ivmap flTo nameMap =
    flip evalState ivmap
  . flip runReaderT (flTo, nameMap)
  . runWriterT


stencilAnalyse :: FAR.NameMap
                 -> F.ProgramFile (FA.Analysis A)
                 -> (String, Result)
stencilAnalyse nameMap pf@(F.ProgramFile mi cm_pus blocks) =
    (dbg1 ++ dbg2, result1 `mappend` result2)
  where
    (_, (dbg1, result1)) = runWriter (transformBiM perPU cm_pus)
    (_, (dbg2, result2)) = runAnalysis ivMap flTo nameMap (descendBiM perBlock blocks)

    -- Run inference per program unit, placing the flowsmap in scope
    perPU :: F.ProgramUnit (FA.Analysis A)
          -> Writer (String, Result) (F.ProgramUnit (FA.Analysis A))

    perPU pu | Just _ <- FA.bBlocks $ F.getAnnotation pu = do
              let pum = descendBiM perBlock pu
              let (pu', log) = runAnalysis ivMap flTo nameMap pum
              tell log
              return pu'
    perPU pu = return pu

    -- induction variable map
    ivMap = FAD.genInductionVarMapByASTBlock beMap gr
    -- perform reaching definitions analysis
    rd    = FAD.reachingDefinitions dm gr
    -- create graph of definition "flows"
    flTo =  FAD.genFlowsToGraph bm dm gr rd

    -- identify every loop by its back-edge
    beMap = FAD.genBackEdgeMap (FAD.dominators gr) gr

    -- get map of AST-Block-ID ==> corresponding AST-Block
    bm    = FAD.genBlockMap pf
    -- get map of program unit ==> basic block graph
    bbm   = FAB.genBBlockMap pf
    -- build the supergraph of global dependency
    sgr   = FAB.genSuperBBGr bbm
    -- extract the supergraph itself
    gr    = FAB.superBBGrGraph sgr

    -- get map of variable name ==> { defining AST-Block-IDs }
    dm    = FAD.genDefMap bm


-- Used to classify an index

classify ixs | any ((==) NonNeighbour) ixs =
    -- Any non-neighour indexing
    mempty { numArrayWrites = 1 }

classify ixs | all (\i -> case i of Neighbour _ _ -> True; _ -> False) ixs
            && any (\i -> case i of Neighbour _ o -> o /= 0; _ -> False) ixs =
    -- All neighbour with some relative
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1 }

classify ixs | any (\i -> case i of Constant _ -> True; _ -> False) ixs =
    -- All relative or constant
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1, numConstArrayWrites = 1 }

classify ixs | isOrigin ixs =
    -- All induction variables
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1, numIVArrayWrites = 1 }


-- Traverse Blocks in the AST and infer stencil specifications
perBlock :: F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))

perBlock b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
    -- On all StExpressionAs that occur in stmt....
    let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                           <- universe stmnt :: [F.Statement (FA.Analysis A)]]
    ivmap <- get
    results <- flip mapM lhses
    -- ... apply the following:
      (\lhs -> do
         case isArraySubscript lhs of
           Just subs -> do
             let lhsIndices = map (ixToNeighbour ivmap) subs
             let r = classify lhsIndices
             if (numNeighbourArrayWrites r > 0) then do
                 -- If the LHS is a neighbourhood index
                 (dbg, r') <- analyseRHS lhsIndices [b]
                 ("At: " ++ show span ++ "\n" ++ dbg) `trace` return ("At: " ++ show span ++ "\n" ++ dbg, r `mappend` r')
             else return ("", r)
           _ -> return mempty)
    tell (mconcat results)
    return b

perBlock b = do
    -- Go inside child blocks
    b' <- descendM (descendBiM perBlock) $ b
    return b'

-- Analyse the RHS of an array subscript
analyseRHS :: [Neighbour]
           -> [F.Block (FA.Analysis A)]
           -> Analysis (String, Result)
analyseRHS lhs blocks = do
    ivs <- get
    (flTo, nameMap) <- ask
    let subscripts = let ?flowsGraph = flTo
                         ?nameMap = nameMap
                     in M.unionsWith (++) $ evalState (mapM (genSubscripts True) blocks) []
    let subscripts' = filterOutFuns nameMap subscripts
    let rhses = M.map (\ixs -> map (map (ixToNeighbour ivs)) ixs) subscripts'
    return $ ("Read arrays: " ++ show (M.keys subscripts) ++ "\n", classifyRHSsubscripts ivs rhses lhs)

-- Filter out any variable names which do not appear in the name map or
-- which in appear in the name map with the same name, indicating they
-- are an instric function, e.g., abs
filterOutFuns nameMap m =
  M.filterWithKey (\k _ ->
     case k `M.lookup` nameMap of
        Nothing           -> False
        Just k' | k == k' -> False
        _                 -> True) m


-- The main function for classifying the RHS subscripts into different
-- kinds of stencil
classifyRHSsubscripts :: FAD.InductionVarMapByASTBlock
                      -> M.Map Variable [[Neighbour]]
                      -> [Neighbour]
                      -> Result
classifyRHSsubscripts ivs rhses lhs
  | rhses == M.empty || anyMap (\rhs -> any (any ((==) NonNeighbour)) rhs) rhses
  = mempty { numLHSButNonNeighbourRHS = 1 }

classifyRHSsubscripts ivs rhses lhs
  | anyMap (\rhs -> not (consistentIVSuse lhs rhs)) rhses
  = mempty { numLHSButInconsistentIVRHS = 1 }

classifyRHSsubscripts ivs rhses lhs =
    mempty { numStencils              = 1
           , numRelativisedRHS        = flag (rhses /= rhsesRel)
           , numContiguousStencils    = flag isContig
           , numSingNonContigStencils = flag (not isContig && (length . M.elems $ rhsesO) == 1)
           , numNoOrigin              = flag (not (allMap (any isOrigin) rhses))
           , numContigLinearStencils  = flag (isContig && allMap (not . snd) rhsesWithMult)
           , dimensionalityHist = selectHist dimensionalities
           , maxDepthHist       = selectHist maxDepth
           , numArraysReadHist  = selectHist numArrays
           , numIndexExprsHist  = selectHist numIndexExprs
           , patternHist        = if isContig then (patterns, m0) else (m0, patterns) }
  where
    m0 = (M.empty, M.empty, M.empty)
    isContig = allMap contiguous rhses
    selectHist = if isContig then contig else nonContig
    rhsesRel = M.map (relativise lhs) rhses
    -- Dimensionality
    dimensionalities = concatHist . map toHist . nub . map length . concat . M.elems $ rhses
    -- Max depth
    rhsesO = M.map (map (filter ((/=) absoluteRep) . fromJust . mapM neighbourToOffset)) rhsesRel
    maxDepth = toHist . maximum0 . M.elems . M.map (maximum0 . map maximum0) $ rhsesO
    -- Num arrays read
    numArrays = toHist . length . M.keys $ rhses
    -- Index exprs
    numIndexExprs = toHist . Data.List.sum . map length . M.elems $ rhses
    -- Patterns
    patterns = mkPatterns . concat . M.elems $ rhsesO
    -- Work out if the stencil is linear or not
    rhsesWithMult = M.map hasDuplicates rhses
    maximum0 [] = 0
    maximum0 xs = maximum xs

-- Predicate on whether an index is at the origin
isOrigin :: [Neighbour] -> Bool
isOrigin nixs = all (\i -> case i of Neighbour _ 0 -> True; _ -> False) nixs

-- Predicat eon whether an index is rectilinearly next to the origin
nextToOrigin :: [Neighbour] -> Bool
nextToOrigin [] = True
nextToOrigin ((Neighbour _ 1):nixs) = isOrigin nixs
nextToOrigin ((Neighbour _ 0):nixs) = nextToOrigin nixs
nextToOrigin _ = False

-- Given two indices, find out if they are (rectilinear) neighbours
neighbouringIxs :: [Neighbour] -> [Neighbour] -> Bool
neighbouringIxs [] [] = True
neighbouringIxs (x : xs) (y : ys) | x == y = neighbouringIxs xs ys
neighbouringIxs ((Neighbour v o) : xs) ((Neighbour v' o') : ys)
  | v == v' && abs (o - o') == 1 && xs == ys = True
neighbouringIxs _ _ = False

-- Given an index 'ns' and a set of indices 'nss',
-- find if 'ns' has a neighbour in 'nss'
hasNeighbouringIx :: [Neighbour] -> [[Neighbour]] -> Bool
hasNeighbouringIx ns [] = False
hasNeighbouringIx ns (ns' : nss) =
  neighbouringIxs ns ns' || hasNeighbouringIx ns nss

-- Contiguous stencil (need not include the origin)
contiguous :: [[Neighbour]] -> Bool
contiguous xs = contiguity' xs
  where
    contiguity' [] = True
    contiguity' (y : ys) | isOrigin y = contiguity' ys
    contiguity' (y : ys) | nextToOrigin y = contiguity' ys
    contiguity' (y : ys) | hasNeighbouringIx y (xs \\ [y]) = contiguity' ys
    contiguity' _ = False

-- Given a list of indices (as a list of offsets), calculate heat maps
-- for one, two and three dimension arrays
mkPatterns :: [[Int]]
           -> (M.Map Int Int, M.Map (Int, Int) Int, M.Map (Int, Int, Int) Int)
mkPatterns ixs = mconcat . map mkPattern $ ixs
  where
    mkPattern [x] = (M.fromList [(x, 1)], M.empty, M.empty)
    mkPattern [x, y] = (M.empty, M.fromList [((x, y), 1)], M.empty)
    mkPattern [x, y, z] = (M.empty, M.empty, M.fromList [((x, y, z), 1)])
    mkPattern _ = (M.empty, M.empty, M.empty)

-- Histogram manipulation
flag True = 1
flag False = 0

-- Generate a singleton histogram for value 'n'
toHist :: Int -> [Int]
toHist n = (replicate n 0) ++ [1]

-- 'zip' together a list of histograms
concatHist [] = []
concatHist [x] = x
concatHist (x:y:xs) = (x `histZip` y) `histZip` (concatHist xs)

-- Injections into representing data for contiguous and non-contiguous
-- stencils
contig, nonContig :: Monoid a => a -> (a, a)
contig n = (n, mempty)
nonContig n = (mempty, n)

-- Predicate transformers on Maps
anyMap p m = M.size (M.filter p m) > 0
allMap p m = M.size (M.filter p m) == M.size m