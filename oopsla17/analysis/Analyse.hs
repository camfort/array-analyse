{-

 Analysis of array usage

 TODO
   * capture single non-contig
   * Figure out whether to bin the different kinds of shape (maybe up to 3D)
            * Tag patterns with either rectilinear,
                                       contiguous composite of rectilinear,
                                       contiguous composite of rectilinear (over ex. origin)
                                       other



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
         let (dbg', result) = classify ivs lhs rhses
         let result' = result { histLengthOfDataflow = toHist dflowLen }
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