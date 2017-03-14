{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

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
import Text.Printf
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
import Data.Maybe
import Data.List
import Data.Monoid
import Debug.Trace

main :: IO ()
main = do
    args <- getArgs
    if (length args >= 1) then
      applyAnalysisToDir (head args)
    else
      putStrLn $ "Please specify a directory on which to apply the analysis"

applyAnalysisToDir :: String -> IO ()
applyAnalysisToDir dir = do
    files <- readParseSrcDir dir []
    debugsAndResults <- mapM applyAnalysisToFile files
    let (dbg, results) = mconcat debugsAndResults
    putStrLn $ dbg
    putStrLn $ show results


-- Result type
data Result = Result {
   numArrayWrites           :: Int,   -- n  where n >= p + m
   numIVArrayWrites         :: Int,   -- p
   numRelativeIVArrayWrites :: Int,   -- m
   numIVOrConstArrayWrites :: Int,    -- p'
   numIVButInconsistentIVRHS :: Int,
   numIVButNonNeighbourRHS   :: Int,
   numContiguousStencils :: Int,      -- c  where c >= d and p >= c
   numLinearStencils     :: Int,      -- d
   dimensionalityHist    :: [Int],    -- h1 where sum(h1) == c
   depthHist             :: [Int],    -- h2 where sum(h2) == c
   numArraysReadHist     :: [Int],
   indexExprsHist        :: [Int],    -- h3
   patternHist           :: (M.Map Int Int
                            , M.Map (Int, Int) Int
                            , M.Map (Int, Int, Int) Int)
                            -- only for 1, 2 and 3 dimensional specs
   } deriving Show


instance Monoid Result where
  mempty = Result 0 0 0 0 0 0 0 0 [] [] [] [] (M.empty, M.empty, M.empty)

  mappend r1 r2 = Result
     { numArrayWrites = numArrayWrites r1 + numArrayWrites r2
     , numIVArrayWrites = numIVArrayWrites r1 + numIVArrayWrites r2
     , numRelativeIVArrayWrites = numRelativeIVArrayWrites r1
                                + numRelativeIVArrayWrites r2

     , numIVOrConstArrayWrites = numIVOrConstArrayWrites r1
                               + numIVOrConstArrayWrites r2

     , numIVButInconsistentIVRHS = numIVButInconsistentIVRHS r1
                                 + numIVButInconsistentIVRHS r2

     , numIVButNonNeighbourRHS = numIVButNonNeighbourRHS r1
                                 + numIVButNonNeighbourRHS r2

     , numContiguousStencils = numContiguousStencils r1
                             + numContiguousStencils r2

     , numLinearStencils = numLinearStencils r1 + numLinearStencils r2
     , dimensionalityHist = histZip (dimensionalityHist r1) (dimensionalityHist r2)
     , depthHist = histZip (depthHist r1) (depthHist r2)
     , numArraysReadHist = histZip (numArraysReadHist r1) (numArraysReadHist r2)
     , indexExprsHist = histZip (indexExprsHist r1) (indexExprsHist r2)
     , patternHist = (M.unionWith (+) (fst3 $ patternHist r1) (fst3 $ patternHist r2)
                , M.unionWith (+) (snd3 $ patternHist r1) (snd3 $ patternHist r2)
                , M.unionWith (+) (thd3 $ patternHist r1) (thd3 $ patternHist r2))
     }
   where
    fst3 (a, b, c) = a
    snd3 (a, b, c) = b
    thd3 (a, b, c) = c

    histZip [] xs = xs
    histZip xs [] = xs
    histZip (x:xs) (y:ys) = (x+y):(histZip xs ys)

applyAnalysisToFile :: (Filename, SourceText, F.ProgramFile A) -> IO (String, Result)
applyAnalysisToFile (filename, _, pf) = do
    putStrLn $ "Analysis on file: " ++ filename
    let pf' = FAR.analyseRenames . FA.initAnalysis $ pf
    let nameMap = FAR.extractNameMap pf'
    return $ stencilAnalyse nameMap (FAB.analyseBBlocks $ pf')

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

classify ixs | any (\i -> neighbourToOffset i == Just o && o /= 0) ixs =
    -- All neighbour with some relative
    mempty { numArrayWrites = 1, numRelativeIVArrayWrites = 1 }

classify ixs | any (\i -> case i of Constant _ -> True; _ -> False) ixs =
    -- All induction variables apart from some constant
    mempty { numArrayWrites = 1, numIVOrConstArrayWrites = 1 }

classify ixs | all (\i -> case i of Neighbour _ 0 -> True; _ -> False) ixs =
    -- All induction variables
    mempty { numArrayWrites = 1, numIVArrayWrites = 1 }

-- Predicate on whether an index is at the origin
isOrigin :: [Neighbour] -> Bool
isOrigin nixs = all (\i -> case i of Neighbour _ 0 -> True; _ -> False) nixs

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
  neighbouringIxs ns ns' || hasNeighbourIx nss

contiguity :: [[Neighbour]] -> Bool
contiguity xs = contiguity' xs
  where
    contiguity' [] = True
    contiguity' (y : ys) | isOrigin y = contiguity' ys
    contiguity' (y : ys) | hasNeighbouringIx y xs = contiguity' ys
    contiguity' _ = False

-- Traverse Blocks in the AST and infer stencil specifications
perBlock :: F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))

perBlock b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
    -- On all StExpressionAssigns that occur in stmt....
    let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                           <- universe stmnt :: [F.Statement (FA.Analysis A)]]
    ivmap <- get
    results <- flip mapM lhses
    -- ... apply the following:
      (\lhs -> do
         case isArraySubscript lhs of
           Just subs -> do
             let indices = map (ixToNeighbour ivmap) subs
             return ("", classify indices)

{- case neighbourIndex ivmap subs of
               Just lhs -> do
                    r <- return $ r { numIVArrayWrites = 1 }
                    -- genSpecsAndReport mode span lhs [b]
                    return ("", r)
               Nothing  ->
                    return ("", r { numRelativeIVArrayWrites = 1}) -}
           -- Not an assign we are interested in -}
           _ -> return mempty)
    tell (mconcat results)
    return b

perBlock b@(F.BlDo ann span lab cname lab' mDoSpec body tlab) = do
    --genSpecsAndReport mode span [] body

    -- descend into the body of the do-statement
    body' <- mapM (descendBiM perBlock) body
    return b

perBlock b = do
    -- Go inside child blocks
    b' <- descendM (descendBiM perBlock) $ b
    return b'

analyseRHS :: [Neighbour]
           -> [F.Block (FA.Analysis A)]
           -> Analysis (String, Result)
analyseRHS lhs blocks = do
    ivmap <- get
    let subscriptsPerArray =
            M.mapWithKey (\v -> indicesToRelativisedOffsets ivs v lhs)
          . M.unionsWith (++)
          $ evalState (mapM (genSubscripts True) blocks) []
    let numArraysRead = length $ fromList subscriptsPerArray
    let r = mempty { numArraysReadHist = toHist numArraysRead }


    tell [ (span, Left specs) ]
    do tell [ (span, Right ("EVALMODE: assign to relative array subscript\
                              \ (tag: tickAssign)","")) ]
         mapM_ (\evalInfo -> tell [ (span, Right evalInfo) ]) evalInfos
         mapM_ (\spec -> if show spec == ""
                          then tell [ (span, Right ("EVALMODE: Cannot make spec\
                                                   \ (tag: emptySpec)","")) ]
                          else return ()) specs
         return specs
      else return specs
-}