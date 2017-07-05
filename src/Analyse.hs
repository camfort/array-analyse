{-

 Analysis of array usage

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
import Camfort.Specification.Stencils.Generate
import Camfort.Specification.Stencils.Annotation
import qualified Camfort.Specification.Stencils.Grammar as Gram
import qualified Camfort.Specification.Stencils.Synthesis as Synth
import Camfort.Analysis.Annotations
import Camfort.Helpers.Vec hiding (length)
import Camfort.Helpers (Filename, SourceText, collect, descendReverseM, descendBiReverseM)
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
import Data.Traversable
import System.Process


import Debug.Trace
import System.Directory
import qualified System.IO.Strict as Strict
import Control.DeepSeq

import Results
import Indices

data Mode = SingleFile | ViewMode | ViewMode2 | NormalMode
                       | CombineMode | DirMode
  deriving (Eq)

main :: IO ()
main = do
    args <- getArgs
    if null args then do
       putStrLn "Example usages:\
                \    array-analysis dir-or-file [excluded-files]\
                \    array-analysis [-b] [-d] dir-or-file [excluded-files]\
                \ where -b means to print pattern bins, and -d is debug mode\
                \\
                \ (restart the analysis with rfile.restart)\
                \    array-analysis RESTART rfile [-b] [-d] dir-or-file [excluded-files]\
                \\
                \ (apply the analysis to a single file)\
                \    array-analysis SINGLE rfile [-b] [-d] dir-or-file [excluded-files]\
                \\
                \ (restart the analysis with rfile.restart and suppress the final file)\
                \    array-analysis VIEW rfile\
                \\
                \ (show just the files that were analysed)\
                \    array-analysis DIRS rfile"
    else do
       let (restart, args', mode) =
            case args of
               (x:y:args') | x == "RESTART" -> (Just y, args', NormalMode)
                           | x == "SINGLE"  -> (Just y, args', SingleFile)
                           | x == "VIEW"    -> (Just y, [],    ViewMode)
                           | x == "VIEW2"   -> (Just y, [],    ViewMode2)
                           | x == "COMBINE"  -> (Nothing, (y:args'), CombineMode)
                           | x == "DIRS"     -> (Just y, [], DirMode)
                           | otherwise      -> (Nothing, args, NormalMode)
               _ -> (Nothing, args, NormalMode)
       case mode of
        CombineMode -> combineMode args'
        DirMode     -> do
            file <- readFile (fromJust restart)
            let (result :: Result) = read file
            mapM putStrLn $ (dirs result)
            return ()
        _ ->
         case args' of
          [] -> applyAnalysisToDir restart mode "" False False []
          [dir]
             -> applyAnalysisToDir restart mode dir False False []

          dir:args@(a1:a2:_)
             -> applyAnalysisToDir restart mode dir (a1 == "-d" || a2 == "-d")
                                          (a1 == "-b" || a2 == "-b")
                                          (filterFlags args)

          dir:args@(a1:_)
             -> applyAnalysisToDir restart mode dir (a1 == "-d")
                                          (a1 == "-b")
                                          (filterFlags args)

          _ -> putStrLn $ "Please specify a directory on which to apply the\
                       \ analysis followed by any number of file names\
                       \ to be excluded."
   where
      filterFlags = filter (\arg -> arg /= "-d" && arg /= "-b")

combineMode :: [String] -> IO ()
combineMode restarts = do
  files <- mapM readFile restarts
  let (results :: [Result]) = map read files
  let result = foldr mappend mempty results
  writeFile "combined.restart" (show result)
  putStrLn $ prettyResults result True
  sloccount <- readProcess "sloccount" (map quotesWhenNeeded $ dirs result) ""
  putStrLn sloccount
  putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
  putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

applyAnalysisToDir :: Maybe String -> Mode -> String -> Bool -> Bool -> [String] -> IO ()
applyAnalysisToDir restart mode dir debug bins excludes = do

    -- See if we have a 'restarts' file to include
    result0 <- case restart of
                 Just restartFile -> do
                        present <- doesFileExist (restartFile ++ ".restart")
                        if present then do
                           resultsString <- Strict.readFile (restartFile ++ ".restart")
                           return $ ((read resultsString) :: Result)
                        else return mempty
                 Nothing -> mempty

    (dbg, result) <-
      case mode of
         ViewMode
            -> return ("", result0)
         ViewMode2
            -> return ("", result0)
         _  -> do files <- readParseSrcDir dir excludes
                  let result1 = result0 `mappend` mempty { dirs = [dir] }
                  foldrM (applyAnalysisToFile (mode, restart) dir) ("", result1) files

    if (debug || mode == SingleFile) then putStrLn $ dbg else return ()

    case mode of
        ViewMode -> do
               putStrLn $ prettyResults result True
               -- Use sloccount to give a total of the physical lines
               sloccount <- readProcess "sloccount" (map quotesWhenNeeded $ dirs result) ""
               putStrLn sloccount
               putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
               putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

        ViewMode2 -> do
               putStrLn $ prettyResults result True
               -- Use sloccount to give a total of the physical lines
               putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
               putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

        NormalMode -> do
               let resultsFile = dir ++ ".array-analysis"
               writeFile resultsFile (show result)
               putStrLn $ prettyResults result bins

        SingleFile -> return ()

    --valid <- resultValidation result
    --if valid then (putStrLn $ "Results were valid") else (putStrLn "Results were invalid")

quotesWhenNeeded xs = if ' ' `elem` xs then "\"" ++ xs ++ "\"" else xs

applyAnalysisToFile :: (Mode, Maybe String)
                    -> String
                    -> (Filename, SourceText, F.ProgramFile A)
                    -> (String, Result)
                    -> IO (String, Result)
applyAnalysisToFile (mode, restart) dir (filename, source, pf) (dbg0, result0) = do
    -- Write results so far to the restart file
    case mode of
      SingleFile -> do
           putStrLn $ prettyResults finalResult False
           writeFile (fromJust restart ++ ".restart") (show finalResult)
      _          ->
           dbg' `deepseq` writeFile (dir ++ ".restart") (show finalResult)

    -- Return results and debugs
    return (finalDebugs, finalResult)
  where
    finalDebugs = dbg0 ++ dbg'
    finalResult = result0 `mappend` result'
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
              let (pu', log) = runAnalysis ivMap flTo pum
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
    (ivs, visitedStmts) <- get
    let label = fromMaybe (-1) (FA.insLabel ann)
    if (label `elem` visitedStmts) then
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

-- Analyse the RHS of any array subscripts in a block
analyseRHS :: [F.Block (FA.Analysis A)]
           -> Analysis (String, M.Map Variable [[F.Index (FA.Analysis A)]], Int)
analyseRHS blocks = do
    (ivs, visitedNodes) <- get
    flTo <- ask
    let (subscripts, visitedNodes') = genSubscripts flTo blocks
    let lenDataflowPath = length . nub $ visitedNodes'
    put (ivs, visitedNodes ++ visitedNodes')
    return $ ("Read arrays: " ++ show (M.keys subscripts) ++ "\n"
             , subscripts
             , lenDataflowPath) -- dataflow
