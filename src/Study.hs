{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import qualified Data.Map as M
import Results
import Data.List
import System.Environment
import Text.Printf

-- This program performs some grouping and analysis on array-analysis
-- data providing the empirical results for the OOPSLA 2017 'Verifying
-- Spatial Properties of Array Computations'

main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Specify a .restart file to analyse"
    [x] -> putStrLn "Specify an analysis you want to run, e.g., hyps"
    (file:study:args) -> do
      resultsString <- readFile file
      let result = read resultsString :: Result
      case study of
        "hyps" -> putStrLn $ hyps result
        "histsplot" -> do
          let camfort h = (M.!) (camfortableResult h) "Camfort"
          writeFile "indexExprs.dat"
              (gnuplotHist (read . head $ args) . camfort . histNumIndexExprs $ result)
          writeFile "dimensionality.dat"
              (gnuplotHist (read . head $ args) . camfort . histDimensionality $ result)
        "hists" ->
          putStrLn $ mapViewTotal "Dimensionality" (histDimensionality result)
           ++ mapViewTotal "Max depth" (histMaxDepth result)
           ++ mapViewTotal "Number of indexing expressions" (M.map (cropHistogram 20) $ histNumIndexExprs result)
           ++ rline' "Length of dataflow path"  (hview . cropHistogram 20 . histLengthOfDataflow $ result)


regroup :: (Ord c, HistogramShow t) => (Cat -> c) -> M.Map Cat t -> M.Map c t
regroup classifier =
  M.fromListWith histZip . map (Control.Arrow.first classifier) . M.assocs

regroupFilter :: (Ord c, HistogramShow t)
              => (Cat -> t -> Bool) -> (Cat -> c) -> M.Map Cat t -> M.Map c t
regroupFilter filter classifier =
  M.fromListWith histZip . map (Control.Arrow.first classifier)
                         . M.assocs
                         . M.filterWithKey filter

resultLine cat dat = showA cat
           ++ replicate (35 - (length (show cat))) ' '
           ++ " & " ++ dat ++ "  \\\\\n"

class ShowA s where
  showA :: s -> String

instance {-# OVERLAPS #-} ShowA String where
  showA = id

instance {-# OVERLAPPABLE #-} Show a => ShowA a where
  showA = show

mapViewT msg map =
       "   " ++ msg ++ ":\n"
    ++ concatMap (\(cat, dat) -> resultLine cat (showPad dat ++ "& "
    ++ twoDP ((cast (dat) / cast (total))*100) ++ "\\%")) (M.assocs map)
    ++ resultLine "Total" (showPad total ++ "&")
    ++ "\n"
  where
    showPad dat = show dat ++ replicate (10 - length (show dat)) ' '
    twoDP = printf "%.2f"
    cast :: Int -> Float
    cast = fromInteger . toInteger
    total = histTotal $ M.elems map

hyps r =
     mapViewT "Hypothesis 1" (countWrapper hypothesis1 r)
  ++ mapViewT "Hypothesis 1 finer" (countWrapper hypothesis1finer r)
  ++ mapViewT "Hypothesis 1 finer - all consts" (countWrapper hypothesis1finerA r)
  ++ mapViewT "Hypothesis 2" (countWrapperFilter hypothesis1filter hypothesis2 r)
  ++ mapViewT "Hypothesis 2 - unfiltered" (countWrapper hypothesis2 r)
  ++ mapViewT "Hypothesis 3" (countWrapperFilter hypothesis1filter hypothesis3 r)
  ++ mapViewT "Hypothesis 3 - unfiltered" (countWrapper hypothesis3 r)

--  ++ mapViewT "Hypothesis 4A" (countWrapper hypothesis4A r)

  ++ mapViewT "Hypothesis 4A" (countWrapper hypothesis4AInconsistents r)
  ++ mapViewT "Hypothesis 4B" (countWrapper hypothesis4B r)
  ++ mapViewT "Hypothesis 4 contig" (countWrapper hypothesis4contig r)
  ++ mapViewT "Hypothesis 4 consistency" (countWrapper hypothesis4consistency r)

  ++ mapViewT "Hypothesis 5" (countWrapper hypothesis5 r)

countWrapper :: Ord c => (Cat -> c) -> Result -> M.Map c Int
countWrapper classifier =
    regroup classifier . counts

countWrapperFilter :: (Ord c) => (Cat -> Int -> Bool) -> (Cat -> c)
                              -> Result
                              -> M.Map c Int
countWrapperFilter filter classifier =
    regroupFilter filter classifier . counts

-- Hypothesis 1 : Loops over arrays mainly read from arrays with a
-- static pattern based on constant offsets from (base or dervied)
-- induction variables;

hypothesis1 :: (Form LHS, Form RHS, Consistency) -> String
hypothesis1 (_, rhs, _) =
  case rhs of
    Affines    c (R (s, _, _, _)) | s /= Other -> "Affine RHS"
    Neighbours c (R (s, _, _, _)) | s /= Other -> "Neigh RHS"
    _                                          -> "Other"

hypothesis1finer :: (Form LHS, Form RHS, Consistency) -> String
hypothesis1finer (_, rhs, _) =
  case rhs of
    Affines    c (R (s, _, _, _)) | s /= Other -> "Affine RHS" ++ hasConst c
    Neighbours c (R (s, _, _, _)) | s /= Other -> "Neigh RHS" ++ hasConst c
    AllConsts                                  -> "All consts"
    _                                          -> "Other"

hypothesis1finerA :: (Form LHS, Form RHS, Consistency) -> String
hypothesis1finerA (_, rhs, _) =
  case rhs of
    Affines    c (R (s, _, _, _)) | s /= Other -> "Affine RHS" ++ hasConst c
    Neighbours c (R (s, _, _, _)) | s /= Other -> "Neigh RHS" ++ hasConst c
    _                                          -> "Other"

hasConst WithConsts = " + constants"
hasConst Normal = " only"

-- Hypothesis 2 : Most loop-array computations of the previous form read
-- from a arrays with a contiguous pattern;

notAllConsts cat _ =
  case cat of
    (_, AllConsts, _) -> False
    _                 -> True

hypothesis1filter cat _ =
  case hypothesis1finer cat of
    "Other" -> False
    "All consts" -> False
    _       -> True

hypothesis2 :: (Form LHS, Form RHS, Consistency) -> String
hypothesis2 (_, rhs, _) =
  case rhs of
    Affines    _ (R (s, _, Contig, _)) | s /= Other -> "rhs(affine,contig)"
    Neighbours _ (R (s, _, Contig, _)) | s /= Other -> "rhs(neigh,contig)"
    Affines    _ (R (s, _, _, _))      | s /= Other -> "rhs(affine,nonContig)"
    Neighbours _ (R (s, _, _, _))      | s /= Other -> "rhs(neigh,nonContig)"
    _                                               -> "other"

-- Hypothesis 3: Most loop-array computations of the previous form read
-- from arrays with a pattern that includes the immediate
-- neighbours (i.e., offset 1 from the induction variable);

includesImmediate OverOrigin = True
includesImmediate StraddleOrigin = True
includesImmediate _              = False

positionString OverOrigin = "origin"
positionString StraddleOrigin = "straddle"
positionString _              = "away"

hypothesis3 :: (Form LHS, Form RHS, Consistency) -> String
hypothesis3 (_, rhs, _) =
  case rhs of
    Affines    _ (R (s, p, Contig, _)) | s /= Other -> "rhs(aff,contig," ++ positionString p ++ ")"
    Neighbours _ (R (s, p, Contig, _)) | s /= Other -> "rhs(neigh,contig," ++ positionString p ++ ")"
    Affines    _ (R (s, p, _, _))      | s /= Other -> "rhs(affine,nonContig," ++ positionString p ++ ")"
    Neighbours _ (R (s, p, _, _))      | s /= Other -> "rhs(neigh,nonContig," ++ positionString p ++ ")"
    _                                               -> "other"

-- Hypothesis 4: Many array computations are \emph{stencil
-- computations}, with a static access pattern, writing
-- to an array at an index based on a constant offset from induction
-- variables.

hypothesis4A :: (Form LHS, Form RHS, Consistency) -> String
hypothesis4A (Subscripts, _, _) = "other"
hypothesis4A (AllConsts, _, _) = "other"
hypothesis4A (lhs, rhs, const) =
  if classRhs rhs == "other" then
    "other"
  else
    "LHS " ++ classLhs ++ ", RHS " ++ classRhs rhs
  where
    classConst = show const
    classLhs =
      case lhs of
        Neighbours _ _ -> "neigh"
        Affines    _ _ -> "affine"
        _              -> show lhs
    classRhs
      (Affines c (R (s, p, con, _))) | s /= Other = "affines"
    classRhs
      (Neighbours c (R (s, p, con, _))) | s /= Other = "neigh"
    classRhs
      _ = "other"

hypothesis4AInconsistents :: (Form LHS, Form RHS, Consistency) -> String
hypothesis4AInconsistents (Subscripts, _, _) = "other"
hypothesis4AInconsistents (AllConsts, _, _) = "other"
hypothesis4AInconsistents (lhs, rhs, const) =
  if classRhs rhs == "other" then
    "other"
  else
    "LHS " ++ classLhs ++ ", RHS " ++ classRhs rhs ++ classConst const
  where
    classConst Inconsistent = ", inconsistent"
    classConst _            = ", *consistent"
    classLhs =
      case lhs of
        Neighbours _ _ -> "neigh"
        Affines    _ _ -> "affine"
        _              -> show lhs
    classRhs
      (Affines c (R (s, p, con, _))) | s /= Other = "affines"
    classRhs
      (Neighbours c (R (s, p, con, _))) | s /= Other = "neigh"
    classRhs
      _ = "other"

hypothesis4B :: (Form LHS, Form RHS, Consistency) -> String
hypothesis4B (Subscripts, _, _) = "other"
hypothesis4B (AllConsts, _, _) = "other"
hypothesis4B (lhs, rhs, const) =
  if classRhs rhs == "other" || const == Inconsistent then
    "other"
  else
    classLhs ++ ", " ++ classRhs rhs ++ ", " ++ classConst
  where
    classConst = show const
    classLhs =
      case lhs of
        Neighbours _ _ -> "neigh"
        Affines    _ _ -> "affine"
        _              -> show lhs
    classRhs
      (Affines c (R (s, p, con, _))) | s /= Other = "affines"
    classRhs
      (Neighbours c (R (s, p, con, _))) | s /= Other = "neigh"
    classRhs
      _ = "other"

hypothesis4contig :: (Form LHS, Form RHS, Consistency) -> String
hypothesis4contig cat@(_, rhs, const) =
  if const /= Inconsistent && hypothesis4A cat /= "other" then
    contiguity rhs
  else
    "other"
  where
    contiguity
      (Affines c (R (s, p, con, _))) | s /= Other = show con
    contiguity
      (Neighbours c (R (s, p, con, _))) | s /= Other = show con
    contiguity _ = ""

hypothesis4consistency :: (Form LHS, Form RHS, Consistency) -> String
hypothesis4consistency cat@(_, rhs, const) =
  if const /= Inconsistent && hypothesis4A cat /= "other" then
    show const
  else
    "other"

hypothesis4 :: (Form LHS, Form RHS, Consistency) -> (Int, HasConstants, HasConstants)
hypothesis4 (lhs, rhs, const) =
  case lhs of
    IVs -> (30 * checkRHS, Normal, hasConsts rhs)
    (Affines   c L)  -> (50 * checkRHS, c, hasConsts rhs)
    (Neighbours c L) -> (70 * checkRHS, c, hasConsts rhs)
    Vars             -> (110 * checkRHS, Normal, hasConsts rhs)
    Subscripts       -> (130 * checkRHS, Normal, hasConsts rhs)
    AllConsts        -> (170 * checkRHS, WithConsts, hasConsts rhs)
  where
    hasConsts (Affines c (R (s, p, Contig, _)))  = c
    hasConsts (Neighbours c (R (s, p, Contig, _))) = c
    hasConsts AllConsts = WithConsts
    hasConsts _ = Normal
    checkRHS =
      case rhs of
        (Affines c (R (s, p, Contig, _))) | s /= Other
                                           && includesImmediate p
                                           && const /= Inconsistent -> 1
        (Neighbours c (R (s, p, Contig, _))) | s /= Other
                                              && includesImmediate p
                                              && const /= Inconsistent -> 2
        _ -> 0


hypothesis4finer :: (Form LHS, Form RHS, Consistency) -> Int
hypothesis4finer (lhs, rhs, const) =
  case lhs of
    IVs -> 0 + checkRHS
    (Affines    _ L) -> 2000 + checkRHS
    (Neighbours _ L) -> 1000 + checkRHS
    _                -> 0
  where
    checkRHS =
      case rhs of
        (Affines _ (R (s, p, Contig, _))) | s /= Other
                                           && includesImmediate p
                                           && constCat > 0 -> 100 + constCat
        (Neighbours _ (R (s, p, Contig, _))) | s /= Other
                                              && includesImmediate p
                                              && constCat > 0 -> 200 + constCat
        _ -> 0
    constCat =
      case const of
        Consistent  rel -> relToInt rel + 1
        Permutation rel -> relToInt rel + 2
        LHSsubset   rel -> relToInt rel + 3
        LHSsuperset rel -> relToInt rel + 4
        Inconsistent    -> 0
    relToInt True = 10
    relToInt _    = 0

-- Hypothesis 5: Many array computations of the regular form
-- read from a particular index just once

hypothesis5 :: (Form LHS, Form RHS, Consistency) -> String
hypothesis5 cat@(lhs, rhs, const) =
  case rhs of
            (Neighbours _ (R (_, _, _, l))) -> "neigh/affine " ++ show l
            (Affines    _ (R (_, _, _, l))) -> "neigh/affine " ++ show l
            _ -> "other"
