{-

 Analysis of array usage

 TODO
   * Detect affine indices (see classifyRHSsubscripts)
   * Figure out whether to bin the different kinds of shape (maybe up to 3D)
            * Tag patterns with either rectilinear,
                                       contiguous composite of rectilinear,
                                       contiguous composite of rectilinear (over ex. origin)
                                       other
   * Collapse first few 'classifyRHSSubscripts'



-}

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
import Camfort.Helpers.Vec hiding (length)
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

import Results
import Indices

main :: IO ()
main = do
    args <- getArgs
    case args of
      [dir]
        -> applyAnalysisToDir (head args) False False []
      dir:args@(a1:a2:_)
        -> applyAnalysisToDir dir (a1 == "-d" || a2 == "-d")
                                  (a1 == "-h" || a2 == "-h") (filterFlags args)
      dir:args@(a1:_)
        -> applyAnalysisToDir dir (a1 == "-d") (a1 == "-h") (filterFlags args)
      _ -> putStrLn $ "Please specify a directory on which to apply the\
                     \ analysis followed by any number of file names\
                     \ to be excluded."
  where
    filterFlags = filter (\arg -> arg /= "-d" && arg /= "-h")

applyAnalysisToDir :: String -> Bool -> Bool -> [String] -> IO ()
applyAnalysisToDir dir debug histograms excludes = do
    files <- readParseSrcDir dir excludes
    let debugsAndResults = map applyAnalysisToFile files
    let (dbg, result)   = mconcat debugsAndResults
    if debug then putStrLn $ dbg else return ()
    putStrLn $ prettyResults result histograms
    valid <- resultValidation result
    if valid then (putStrLn $ "Results were valid") else (putStrLn "Results were invalid")

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
                    (State (FAD.InductionVarMapByASTBlock, [Int])))
                    -- A map of induction variables
                    -- and a list of already visisted statements

runAnalysis :: FAD.InductionVarMapByASTBlock
            -> FAD.FlowsGraph A
            -> FAR.NameMap
            -> Analysis a
            -> (a, (String, Result))
runAnalysis ivmap flTo nameMap =
    flip evalState (ivmap, [])
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


{-
-- Used to classify an index

classifyLHS ixs | any ((==) NonNeighbour) ixs =
    -- Any non-neighour indexing
    mempty { numArrayWrites = 1 }

classifyLHS ixs | all (\i -> case i of Neighbour _ _ -> True; _ -> False) ixs
            && any (\i -> case i of Neighbour _ o -> o /= 0; _ -> False) ixs =
    -- All neighbour with some relative
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1 }

classifyLHS ixs | any (\i -> case i of Constant _ -> True; _ -> False) ixs =
    -- All relative or constant
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1, numConstArrayWrites = 1 }

classifyLHS ixs | isOrigin ixs =
    -- All induction variables
    mempty { numArrayWrites = 1, numNeighbourArrayWrites = 1, numIVArrayWrites = 1 }
-}


-- Traverse Blocks in the AST and infer stencil specifications
-- Note that this should be applied by `descendBiM`, as it does its
-- own inner traversal and relies on the order in which blocks are visited
perBlock :: F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))

perBlock b@(F.BlDo aan span lab cname lab' mDoSpec body tlab) = do
   -- Inside a DO block
   -- Process the inside of a DO block in reverse order
   mapM perBlockInnerDo (reverse body)
   return b

perBlock b = do
    -- Go inside child blocks
    b' <- descendM (descendBiM perBlock) b
    return b'

perBlockInnerDo :: F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))
perBlockInnerDo b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
    -- On all StExpressionAssign that occur in a stmt within a DO
    let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                           <- universe stmnt :: [F.Statement (FA.Analysis A)]]
    (ivs, visistedStmts) <- get
    let label = fromMaybe (-1) (FA.insLabel ann)
    if (label `elem` visistedStmts) then
      -- This statement has been part of an existing dataflow path
      return b

    else do
      results <- forM lhses $ \lhs -> do
         (dbg, rhses, dflowLen) <- analyseRHS [b]
         let (dbg', cat, result) = classify ivs lhs rhses
         let result' = result { histLengthOfDataflow =
                                   M.fromList [(cat, toHist dflowLen)] }
         return ("At: " ++ show span ++ "\n" ++ dbg ++ dbg', result')
      tell (mconcat results)
      return b

perBlockInnerDo b = do
   -- Go inside other kinds of block (like case/if)
   b' <- descendM (descendBiM perBlockInnerDo) b
   return b'

-- Analyse the RHS of any array subscripts in a block
analyseRHS :: [F.Block (FA.Analysis A)]
           -> Analysis (String, M.Map Variable [[F.Index (FA.Analysis A)]], Int)
analyseRHS blocks = do
    (ivs, visitedNodes) <- get
    (flTo, nameMap) <- ask
    let (maps, visitedNodes') =
         let ?flowsGraph = flTo
             ?nameMap = nameMap
         in runState (mapM (genSubscripts True) blocks) []
    let subscripts = M.unionsWith (++) maps
    let subscripts' = filterOutFuns nameMap subscripts
    let lenDataflowPath = length . nub $ visitedNodes'
    put (ivs, visitedNodes ++ visitedNodes')
    return $ ("Read arrays: " ++ show (M.keys subscripts) ++ "\n"
             , subscripts'
             , lenDataflowPath) -- dataflow

-- Filter out any variable names which do not appear in the name map or
-- which in appear in the name map with the same name, indicating they
-- are an instric function, e.g., abs
filterOutFuns nameMap m =
  M.filterWithKey (\k _ ->
     case k `M.lookup` nameMap of
        Nothing           -> False
        Just k' | k == k' -> False
        _                 -> True) m

boolToContig True  = Contig
boolToContig False = NonContig

{-
-- The main function for classifying the RHS subscripts into different
-- kinds of stencil
classifyRHSsubscripts :: Kind
                      -> M.Map Variable [[Neighbour]]
                      -> [Neighbour]
                      -> Int
                      -> Result
classifyRHSsubscripts Stencil rhses _ dflowLen
  | rhses == M.empty || anyMap (\rhs -> any (any ((==) NonNeighbour)) rhs) rhses
  = mempty { numLHSButNonNeighbourRHS = 1
           , histLengthOfDataflow = M.fromList [((Stencil, NonContig), toHist dflowLen)]}

classifyRHSsubscripts Stencil rhses lhs dflowLen
  | anyMap (\rhs -> not (consistentIVSuse lhs rhs)) rhses
  = mempty { numLHSButInconsistentIVRHS = 1
           , histLengthOfDataflow = M.fromList [((Stencil, NonContig), toHist dflowLen)]}

classifyRHSsubscripts kind rhses lhs dflowLen =
    mempty { numOverall               = M.fromList [(cat, 1)]
           , numStencilRelativisedRHS = flag (isStencil && rhses /= rhsesRel)
           , numSingNonContigStencils = flag (isStencil
                                             && not isContig
                                             && (length . concat . M.elems $ rhsesO) == 1)
           , numNoOrigin              = M.fromList [(cat, flag (not (allMap (any isOrigin) rhses)))]
           , numLinear                = M.fromList [(cat, flag (allMap (not . snd) rhsesWithMult))]
           , histDimensionality       = M.fromList [(cat, dimensionalities)]
           , histMaxDepth             = M.fromList [(cat, maxDepth)]
           , histNumArraysRead        = M.fromList [(cat, numArrays)]
           , histNumIndexExprs        = M.fromList [(cat, numIndexExprs)]
           , histLengthOfDataflow     = M.fromList [(cat, toHist dflowLen)]
           , histPatterns             = M.fromList [(cat, patterns)] }
  where
    cat = (kind, contig)
    m0 = (M.empty, M.empty, M.empty)
    contig   = boolToContig isContig
    isContig = allMap contiguous rhses
    isStencil = kind == Stencil

    -- Relativise the rhses if this is a stencil
    rhsesRel = if isStencil then M.map (relativise lhs) rhses else rhses
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
    -- Work out if the pattern is linear or not
    rhsesWithMult = M.map hasDuplicates rhses
    maximum0 [] = 0
    maximum0 xs = maximum xs
-}

-- Predicate on whether an index is at the origin
isOrigin :: [Neighbour] -> Bool
isOrigin nixs = all (\i -> case i of Neighbour _ 0 -> True; _ -> False) nixs

-- Predicate on whether an index is rectilinearly next to the origin
nextToOrigin :: [Neighbour] -> Bool
nextToOrigin [] = True
nextToOrigin ((Neighbour _ 1):nixs) = isOrigin nixs
nextToOrigin ((Neighbour _ (-1)):nixs) = isOrigin nixs
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
--contig, nonContig :: Monoid a => a -> (a, a)
--contig n = (n, mempty)
--nonContig n = (mempty, n)

-- Predicate transformers on Maps
anyMap p m = M.size (M.filter p m) > 0
allMap p m = M.size (M.filter p m) == M.size m