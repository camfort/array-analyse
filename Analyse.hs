{-

 Analysis of array usage

 TODO
   * capture single non-contig
   * Figure out whether to bin the different kinds of shape (maybe up to 3D)

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
import qualified Data.Generics.Str as Str
import Data.Graph.Inductive.Graph hiding (isEmpty)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.ByteString.Char8 as B
import Data.Maybe
import Data.List
import Data.Monoid
import Data.Traversable

import Debug.Trace
import System.Directory
import qualified System.IO.Strict as Strict
import Control.DeepSeq

import Results
import Indices

main :: IO ()
main = do
    args <- getArgs
    let (restart, args') = case args of
                             (x:y:args') | x == "RESTART" -> (Just y, args')
                             _                            -> (Nothing, args)
    case args' of
      [dir]
        -> applyAnalysisToDir restart dir False False []

      dir:args@(a1:a2:_)
        -> applyAnalysisToDir restart dir (a1 == "-d" || a2 == "-d")
                                          (a1 == "-b" || a2 == "-b")
                                          (filterFlags args)

      dir:args@(a1:_)
        -> applyAnalysisToDir restart dir (a1 == "-d")
                                          (a1 == "-b")
                                          (filterFlags args)

      _ -> putStrLn $ "Please specify a directory on which to apply the\
                     \ analysis followed by any number of file names\
                     \ to be excluded."
  where
    filterFlags = filter (\arg -> arg /= "-d" && arg /= "-b")

applyAnalysisToDir :: Maybe String -> String -> Bool -> Bool -> [String] -> IO ()
applyAnalysisToDir restart dir debug bins excludes = do
    files <- readParseSrcDir dir excludes
    let resultsFile = dir ++ ".stencil-analysis"

    -- See if we have a 'restarts' file to include
    result0 <- case restart of
                 Just restartFile -> do
                        resultsString <- Strict.readFile (restartFile ++ ".restart")
                        return $ ((read resultsString) :: Result)
                 Nothing -> mempty

    (dbg, result) <- foldrM (applyAnalysisToFile dir) ("", result0) files

    writeFile resultsFile (show result)
    if debug then putStrLn $ dbg else return ()
    putStrLn $ prettyResults result bins
    valid <- resultValidation result
    if valid then (putStrLn $ "Results were valid") else (putStrLn "Results were invalid")

applyAnalysisToFile :: String
                    -> (Filename, SourceText, F.ProgramFile A)
                    -> (String, Result)
                    -> IO (String, Result)
applyAnalysisToFile dir (filename, source, pf) (dbg0, result0) = do
    -- Write results so far to the restart file
    dbg' `deepseq` writeFile (dir ++ ".restart") (show (result0 `mappend` result'))
    -- Return results and debugs
    return (dbg0 ++ dbg', result0 `mappend` result')
  where
    lines = length $ B.lines source
    pf' = FAR.analyseRenames . FA.initAnalysis $ pf
    nameMap = FAR.extractNameMap pf'
    result' = result { numLines = lines }
    dbg' = "Analysis on file: " ++ filename ++ "\n" ++ dbg
    (dbg, result) = stencilAnalyse nameMap . FAB.analyseBBlocks $ pf'

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
    (_, (dbg2, result2)) = runAnalysis ivMap flTo nameMap
                             (descendBiM (perBlock False) blocks)

    -- Run inference per program unit, placing the flowsmap in scope
    perPU :: F.ProgramUnit (FA.Analysis A)
          -> Writer (String, Result) (F.ProgramUnit (FA.Analysis A))

    perPU pu | Just _ <- FA.bBlocks $ F.getAnnotation pu = do
              let pum = descendBiM (perBlock False) pu
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
perBlock :: Bool -> F.Block (FA.Analysis A) -> Analysis (F.Block (FA.Analysis A))

perBlock inDo b@(F.BlDo ann span lab cname lab' mDoSpec body tlab) = do
   -- Inside a DO block
   -- Process the inside of a DO block in reverse order
   mapM (perBlock True) (reverse body)
   return b

perBlock False b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
  -- Detect subscript range expressions outside loops
  let lhses = [lhs | (F.StExpressionAssign _ _ lhs _)
                         <- universe stmnt :: [F.Statement (FA.Analysis A)]]
  -- Find subscript ranges involved
  let subscriptRanges = [r | r@(F.IxRange {}) <- universeBi lhses :: [F.Index (FA.Analysis A)]]
  if (null subscriptRanges)
    then return b
     -- Use the normal 'inner do' mode if this looks like a ranged-based expression
    else perBlock True b

perBlock True b@(F.BlStatement ann span@(FU.SrcSpan lp up) _ stmnt) = do
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
         let result' = result { histLengthOfDataflow = toHist (dflowLen - 1) }
         return ("At: " ++ show span ++ "\n" ++ dbg ++ dbg', result')
      tell (mconcat results)
      return b

perBlock inDo b = do
    -- Go inside child blocks
    b' <- descendReverseM (descendBiReverseM (perBlock inDo)) b
    return b'

-- Custom version of descend that process tree in reverse order

descendReverseM :: (Data on, Monad m) => (on -> m on) -> on -> m on
descendReverseM f x =
    liftM generate . fmap unwrapReverse . traverse f . Reverse $ current
  where (current, generate) = uniplate x

descendBiReverseM :: (Data from, Data to, Monad m) => (to -> m to) -> from -> m from
descendBiReverseM f x =
    liftM generate . fmap unwrapReverse . traverse f . Reverse $ current
  where (current, generate) = biplate x

data Reverse f a = Reverse { unwrapReverse :: f a }

instance Functor (Reverse Str.Str) where
    fmap f (Reverse s) = Reverse (fmap f s)

instance Foldable (Reverse Str.Str) where
    foldMap f (Reverse x) = foldMap f x

instance Traversable (Reverse Str.Str) where
    traverse f (Reverse Str.Zero) = pure $ Reverse Str.Zero
    traverse f (Reverse (Str.One x)) = (Reverse . Str.One) <$> f x
    traverse f (Reverse (Str.Two x y)) = (\y x -> Reverse $ Str.Two x y)
                             <$> (fmap unwrapReverse . traverse f . Reverse $ y)
                             <*> (fmap unwrapReverse . traverse f . Reverse $ x)

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
    return $ ("Read arrays: " ++ show (M.keys subscripts') ++ "\n"
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