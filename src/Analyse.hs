{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}


module Analyse where

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
import Camfort.Specification.Stencils.Generate
import Camfort.Specification.Stencils.Annotation
import qualified Camfort.Specification.Stencils.Grammar as Gram
import qualified Camfort.Specification.Stencils.Synthesis as Synth
import Camfort.Analysis.Annotations
import Camfort.Helpers.Vec hiding (length)
import Camfort.Helpers (Filename, SourceText, collect, descendReverseM, descendBiReverseM)
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
import Data.Traversable
import System.Process


import Debug.Trace
import qualified System.IO.Strict as Strict
import Control.DeepSeq

import Results
import Indices


data Mode = SingleFile | ViewMode | SlocMode | NormalMode
                       | CombineMode | DirMode | CmpMode
  deriving (Eq)


applyAnalysisToFile :: (Mode, Maybe String)
                    -> String
                    -> (Filename, SourceText, F.ProgramFile A)
                    -> (String, Result)
                    -> IO (String, Result)
applyAnalysisToFile (mode, restart) dir (filename, source, pf) (dbg0, result0) = do
    case mode of
       SingleFile ->
          if filename `elem` dirs result0
          then do
            putStrLn $ "Skipping " ++ filename ++ " as already analysed"
            return (dbg0, result0)
          else do
            putStrLn $ prettyResults finalResult False
            -- Write results so far to the restart file
            writeFile (fromJust restart ++ ".restart") (show finalResult)
            return (finalDebugs, finalResult)
       _ -> do
         dbg' `deepseq` writeFile (dir ++ ".restart") (show finalResult)
         return (finalDebugs, finalResult)
  where
    finalDebugs = dbg0 ++ dbg'
    finalResult = result0 `mappend` result' `mappend` mempty { dirs = [filename] }
    lines = length $ B.lines source
    pf' = FAR.analyseRenames . FA.initAnalysis $ pf
    result' = result { numLines = lines }
    dbg' = "Analysis on file: " ++ filename ++ "\n" ++ dbg
    (dbg, result) = arrayAnalyse . FAB.analyseBBlocks $ pf'

-- The core of the analysis works within this monad
type Analysis = WriterT (String, Result)
                 (ReaderT (FAD.FlowsGraph A)
                    (State (FAD.InductionVarMapByASTBlock, [Int])))
                    -- A map of induction variables
                    -- and a list of already visisted statements

runAnalysis :: FAD.InductionVarMapByASTBlock
            -> FAD.FlowsGraph A
            -> Analysis a
            -> (a, (String, Result))
runAnalysis ivmap flTo  =
    flip evalState (ivmap, [])
  . flip runReaderT flTo
  . runWriterT


arrayAnalyse :: F.ProgramFile (FA.Analysis A)
             -> (String, Result)
arrayAnalyse pf@(F.ProgramFile mi cm_pus) =
    (dbg, result)
  where
    (_, (dbg, result)) = runWriter (transformBiM perPU cm_pus)

    -- Run inference per program unit, placing the flowsmap in scope
    perPU :: F.ProgramUnit (FA.Analysis A)
          -> Writer (String, Result) (F.ProgramUnit (FA.Analysis A))

    perPU pu | Just _ <- FA.bBlocks $ F.getAnnotation pu = do
              let pum = descendBiM (perBlock False) pu
                  -- perform reaching definitions analysis
                  rd = FAD.reachingDefinitions dm gr
                  Just gr = M.lookup (FA.puName pu) bbm
                  -- create graph of definition "flows"
                  flTo = FAD.genFlowsToGraph bm dm gr rd
                  -- identify every loop by its back-edge
                  beMap = FAD.genBackEdgeMap (FAD.dominators gr) gr
                  -- induction variable map
                  ivMap = FAD.genInductionVarMapByASTBlock beMap gr
                  (pu', log) = runAnalysis ivMap flTo pum
              tell log
              return pu'
    perPU pu = return pu



perBlock :: Bool -> F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))

perBlock inDo b@(F.BlDo ann span lab cname lab' mDoSpec body tlab) = do
   -- Inside a DO block
   -- Process the inside of a DO block in reverse order
   mapM_ (perBlock True) (reverse body)
   return b

perBlock False b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
  -- Detect subscript range expressions outside loops
  let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                         <- universe stmnt :: [F.Statement (FA.Analysis A)]]
  -- Find subscript ranges involved
  let subscriptRanges = [r | r@F.IxRange {} <- universeBi lhses :: [F.Index (FA.Analysis A)]]
  if null subscriptRanges
    then return b
     -- Use the normal 'inner do' mode if this looks like a ranged-based expression
    else perBlock True b

perBlock True b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
    -- On all StExpressionAssign that occur in a stmt within a DO
    let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                           <- universe stmnt :: [F.Statement (FA.Analysis A)]]
    (ivs, visitedStmts) <- get
    let label = fromMaybe (-1) (FA.insLabel ann)
    if label `elem` visitedStmts then
      -- This statement has been part of an existing dataflow path
      return b

    else do
      results <- forM lhses $ \lhs -> do
         (dbg, rhses, dflowLen) <- analyseRHS [b]
         let (dbg', result) = classify ivs lhs rhses
         let result' = result { histLengthOfDataflow = toHist (dflowLen - 1) }
         return ("At: " ++ show span ++ "\n" ++ dbg ++ dbg', result')
      tell (mconcat results)
      return b

perBlock inDo b =
    -- Go inside child blocks
    descendReverseM (descendBiReverseM (perBlock inDo)) b

-- Analyse the RHS of any array subscripts in a block
analyseRHS :: [F.Block (FA.Analysis A)]
           -> Analysis (String, M.Map Variable [[F.Index (FA.Analysis A)]], Int)
analyseRHS blocks = do
    (ivs, visitedNodes) <- get
    flTo <- ask
    let (subscripts, visitedNodes') = genSubscripts flTo blocks
    let lenDataflowPath = length . nub $ visitedNodes'
    put (ivs, visitedNodes ++ visitedNodes')
    return ("Read arrays: " ++ show (M.keys subscripts) ++ "\n"
             , subscripts
             , lenDataflowPath) -- dataflow
