{- Analyse array programming idioms in Fortran code. Designed for large code
base code analysis, providing intermediate files so that the analysis can be
split up, paused, and restarted -}

{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.List
import System.Environment
import System.Directory

import Control.Monad (when)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Product)

import Camfort.Analysis.CommentAnnotator
import Camfort.Input
import qualified Camfort.Output as O

import Data.Maybe (fromJust)
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
    if null args then
       putStrLn "Usage:\n\
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
                \   array-analysis COMBINE rfile1 rfile2...rfilen\n"
    else do
       let (restart, args', mode) =
            case args of
               (x:y:args') | x == "RESTART"  -> (Just y, args', NormalMode)
                           | x == "SINGLE"   -> (Just y, args', SingleFile)
                           | x == "VIEW"     -> (Just y, [],    ViewMode)
                           | x == "SLOC"     -> (Just y, [],    SlocMode)
                           | x == "COMBINE"  -> (Nothing, y:args', CombineMode)
                           | x == "DIRS"     -> (Just y, [], DirMode)
                           | otherwise       -> (Nothing, args, NormalMode)
               _                             -> (Nothing, args, NormalMode)
       case mode of
        CombineMode -> combineMode args'
        DirMode     -> do
            file <- readFile (fromJust restart)
            let (result :: Result) = read file
            mapM_ putStrLn (dirs result)

        -- All other modes
        _ -> do
            let binFlag   = "-b" `elem` args
            let debugFlag = "-d" `elem` args
            let dir       = if null args then "" else head args
            applyAnalysisToDir restart mode dir debugFlag binFlag (filterFlags args)

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

    -- See if we have a 'restart' file to include
    result0 <- case restart of
                 Just restartFile -> do
                        present <- doesFileExist (restartFile ++ ".restart")
                        if present then do
                           resultsString <- Strict.readFile (restartFile ++ ".restart")
                           return ((read resultsString) :: Result)
                        else return mempty
                 Nothing -> mempty

    (dbg, result) <-
      case mode of
         ViewMode -> return ("", result0)
         SlocMode -> return ("", result0)
         _        -> do
             files <- readParseSrcDir dir excludes
             let result1 = result0 `mappend` mempty { dirs = [dir] }
             foldrM (applyAnalysisToFile (mode, restart) dir) ("", result1) files

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
               let resultsFile = dir ++ ".array-analysis"
               writeFile resultsFile (show result)
               putStrLn $ prettyResults result bins

        SingleFile -> return ()


quotesWhenNeeded xs = if ' ' `elem` xs then "\"" ++ xs ++ "\"" else xs