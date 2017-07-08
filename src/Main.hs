{- Analyse array programming idioms in Fortran code. Designed for large code
base code analysis, providing intermediate files so that the analysis can be
split up, paused, and restarted -}

{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Environment
import System.Directory

import Control.Monad (when)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Product)

import Camfort.Analysis.CommentAnnotator
import Camfort.Input
import qualified Camfort.Output as O

import qualified Data.Map as M
import Data.Function (on)
import Data.Maybe (fromJust)
import Data.List
import Data.Foldable
import System.Process

import Debug.Trace
import qualified System.IO.Strict as Strict
import Control.DeepSeq

import Results
import Analyse

main :: IO ()
main = do
    args <- getArgs
    if null args then usage
    else do
       modeSwitch <-
            case args of
              ("CMP":arg1:arg2:_) -> do
                    -- Compare two restart files, generally they are considered "equal" if
                    -- they have the same data apart from the 'dir' field which records the files
                    -- which may change depending on where the analysis was run
                    res1 <- readRestart arg1
                    res2 <- readRestart arg2
                    putStrLn $ "Dirs:\t" ++ (show (on (==) dirs res1 res2))
                    putStrLn $ "#lines:\t" ++ (show (on (==) numLines res1 res2))
                    putStrLn $ "histDimensionality:\t" ++ (show (on (==) histDimensionality res1 res2))
                    putStrLn $ "histMaxDepth:\t" ++ (show (on (==) histMaxDepth res1 res2))
                    putStrLn $ "histNumIndexExprs:\t" ++ (show (on (==) histNumIndexExprs res1 res2))
                    putStrLn $ "histNumArraysRead:\t" ++ (show (on (==) histNumArraysRead res1 res2))
                    putStrLn $ "histLengthOfDataflow:\t" ++ (show (on (==) histLengthOfDataflow res1 res2))
                    putStrLn $ "histAffineScale:\t" ++ (show (on (==) histAffineScale res1 res2))
                    putStrLn $ "patternBin1D:\t" ++ (show (on (==) patternBin1D res1 res2))
                    putStrLn $ "patternBin2D:\t" ++ (show (on (==) patternBin2D res1 res2))
                    putStrLn $ "patternBin3D:\t" ++ (show (on (==) patternBin3D res1 res2))

                    let res1' = res1 { dirs = [] }
                    let res2' = res2 { dirs = [] }
                    putStrLn $ "all-but-dirs:\t" ++ (show $ res1' == res2')
                    return Nothing

              ("COMBINE":args) -> do
                    combineMode args
                    return Nothing

              ("DIRS":rfile:_) -> do
                    result <- readRestart rfile
                    mapM_ putStrLn (dirs result)
                    return Nothing

              (mode:arg:args')
                    | mode == "SINGLE" -> return $ Just (Just arg, args', SingleFile)
                    | mode == "VIEW"   -> return $ Just (Just arg, [],    ViewMode)
                    | mode == "SLOC"   -> return $ Just (Just arg, [],    SlocMode)
                    | mode == "CMP"    -> return $ Just (Nothing, arg:args', CmpMode)
              _ -> return $ Just (Nothing, args, NormalMode)
       case modeSwitch of
         Nothing -> return ()
         Just (restart, args, mode) -> do
            let binFlag   = "-b" `elem` args
            let debugFlag = "-d" `elem` args
            let dir       = if null args then "" else head args
            applyAnalysisToDir restart mode dir debugFlag binFlag (filterFlags args)

usage = putStrLn "Usage:\n\
                \    array-analysis [MODE] [OPTIONS] dir-or-file [excluded-files]\n\
                \\n\
                \Options: -b \t print pattern bins\n\
                \         -d \t debug mode\n\
                \\n\
                \Modes:\n\
                \  Restart the analysis with the intermediate file rfile.restart:\n\
                \    array-analysis RESTART rfile [OPTIONS] dir-or-file [excluded-files]\n\
                \\n\
                \ Apply the analysis to a single file with restart file rfile.restart:\n\
                \    array-analysis SINGLE rfile [OPTIONS] dir-or-file [excluded-files]\n\
                \\n\
                \ Restart the analysis with rfile.restart and suppress the final result file \n\
                \    array-analysis VIEW rfile\n\
                \\n\
                \ Perform sloccount on the files contributing to rfile.restart\n\
                \    array-analysis SLOC rfile\n\
                \\n\
                \ Show just the file names contributed to the restart file rfile.restart\n\
                \    array-analysis DIRS rfile\n\
                \\n\
                \ Combine restart files\n\
                \   array-analysis COMBINE rfile1 rfile2...rfilen\n\
                \\n\
                \ Compare two restart files\n\
                \   array-analysis CMP rfile1 rfile2\n"

filterFlags = filter (\arg -> arg /= "-d" && arg /= "-b")

combineMode :: [String] -> IO ()
combineMode restarts = do
  results <- mapM readRestart restarts
  let result = foldr mappend mempty results
  writeFile "combined.restart" (show result)
  putStrLn $ prettyResults result True
  sloccount <- readProcess "sloccount" (map quotesWhenNeeded $ dirs result) ""
  putStrLn sloccount
  putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
  putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

readRestart :: String -> IO Result
readRestart fname = do
   present <- doesFileExist (fname ++ ".restart")
   if present then do
      resultsString <- Strict.readFile (fname ++ ".restart")
      return ((read resultsString) :: Result)
   else do
     mempty -- error $ fname ++ " not found."

applyAnalysisToDir :: Maybe String -> Mode -> String -> Bool -> Bool -> [String] -> IO ()
applyAnalysisToDir restart mode dir debug bins excludes = do

    -- See if we have a 'restart' file to include
    result0 <- case restart of
                 Just restartFile -> readRestart restartFile
                 Nothing          -> mempty

    (dbg, result) <-
      case mode of
         ViewMode -> return ("", result0)
         SlocMode -> return ("", result0)
         _        -> do
             files <- readParseSrcDir dir excludes
             foldrM (applyAnalysisToFile (mode, restart) dir) ("", result0) files

    when (debug || mode == SingleFile) $ putStrLn dbg

    case mode of
        SlocMode -> do
               -- Use sloccount to give a total of the physical lines
               sloccount <- readProcess "sloccount" (map quotesWhenNeeded $ dirs result) ""
               putStrLn sloccount
               putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
               putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

        ViewMode -> do
               putStrLn $ prettyResults result True
               putStrLn $ "Files/dirs counted:" ++ (show . length . dirs $ result)
               putStrLn $ "Raw count (parsed):" ++ (show . numLines $ result)

        NormalMode -> do
               putStrLn $ prettyResults result bins

        SingleFile -> return ()


quotesWhenNeeded xs = if ' ' `elem` xs then "\"" ++ xs ++ "\"" else xs