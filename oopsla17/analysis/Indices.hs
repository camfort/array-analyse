{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Indices where

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

import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Foldable
import Data.List
import Data.Maybe
import Debug.Trace

import Neighbour
import Results


-- Main function for classifying array statements
classify :: FAD.InductionVarMapByASTBlock
         -> F.Expression (FA.Analysis A)
         -> M.Map Variable [[F.Index (FA.Analysis A)]]
         -> (String, Result)
classify ivs lhs rhses = (debug, resultN)
  where
    debug = ""

    -- Num arrays read
    numArrays = length . M.keys $ rhses

    resultN = result { histNumArraysRead = toHist numArrays }
    result = foldr1 mappend (map (classifyArrayCode ivs lhs) (M.elems rhses))

(><) :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
f >< g = \(x, y) -> (f x, g y)

-- LHS are neighbours
classifyArrayCode ivs lhs rhses =
    result
  where
    cat    = (lhsForm, rhsForm, consistency)
    result1 = mempty { histMaxDepth = M.fromList [(cat, toHist maxDepth),
                                                  (cat, toHist minDepth)]
                     , histDimensionality = mkHist cat dim
                     , histNumIndexExprs  = mkHist cat . toHist . length $ rhses
                     , counts             = mkHist cat 1 }

    result2  = case affineScales of
                Nothing -> result1
                Just scales -> result1 { histAffineScale = concatHist (map toHist scales) }
    -- pattern bins
    result = case maximum . map length $ rhses of
               1 -> result2 { patternBin1D = M.fromList [(to1D pattern, 1)] }
               2 -> result2 { patternBin2D = M.fromList [(to2D pattern, 1)] }
               3 -> result2 { patternBin3D = M.fromList [(to3D pattern, 1)] }
               _ -> result2
    ------------
    lhsRep = case isArraySubscript lhs of
                  Nothing -> Nothing
                  Just lhsSubscript -> Just $ classifyIxs ivs [lhsSubscript]
    rhsRep = classifyIxs ivs rhses
    (consistency, rhsRepRel) =
      case (lhsRep, rhsRep) of
        (Nothing, _) -> (Consistent False, rhsRep)
        (Just (Neigh [lhsAs]), Neigh rhsAs)   -> (id >< Neigh) $ checkConsistency lhsAs rhsAs
        (Just (Affine [lhsAs]), Affine rhsAs) -> (id >< Affine) $ checkConsistency lhsAs rhsAs
        (_, _)                                -> (Inconsistent, rhsRep)
    ------------
    lhsForm = case lhsRep of
                Nothing -> Vars
                Just Subscript  -> Subscripts
                Just (Affine as) -> if allIVs as then IVs else Affines (hasConstants as) L
                Just (Neigh  ns) -> if allIVs ns then IVs else Neighbours (hasConstants ns) L
    rhsForm = case rhsRep of
                Subscript -> Subscripts
                Affine as  -> Affines (hasConstants as) (R rhsPhysical)
                Neigh  ns  -> Neighbours (hasConstants ns) (R rhsPhysical)
    rhsPhysical = (shape, position, boolToContig contiguity, boolToReuse (not nonLinear))
    ------------
    neighbourisedRhs = case rhsRepRel of
                         Subscript -> []
                         Affine as -> map (map affineToNeighbour) as
                         Neigh  ns -> ns
    (shape, position) = shapeAndPosition neighbourisedRhs
    -- Work out if the pattern is linear or not
    (_, nonLinear) = hasDuplicates neighbourisedRhs
    -- Contiguity
    contiguity = contiguous neighbourisedRhs
    -- Calculate the max depth (from relativised)

    ------------ Other properties
    -- Dimensionality
    dim = concatHist . map toHist . nub . map length $ rhses

    rhsOffsets = map (fromJust . mapM neighbourToOffset) neighbourisedRhs

    -- Max and min depth
    (maxDepth, minDepth) = (maximum' >< minimum') . unzip . map (maxMin . filter (/= absoluteRep)) $ rhsOffsets
    maxMin x = (maximum' x, minimum' x)

    maximum' :: (Ord a, Bounded a) => [a] -> a
    maximum' [] = minBound
    maximum' xs = maximum xs

    minimum' :: (Ord a, Bounded a) => [a] -> a
    minimum' [] = maxBound
    minimum' xs = minimum xs

    -- Affine scalar multiples
    affineScales = case rhsRep of
                      Affine as -> Just . nub . map (\(a, _, _) -> a) . concat $ as
                      _         -> Nothing
    -- Pattern bin
    pattern = sort . nub . map (map shrinkAbsoluteRep) $ rhsOffsets

    shrinkAbsoluteRep x | x == absoluteRep = 137
    shrinkAbsoluteRep x                    = x


checkConsistency :: (Eq t, Relativise t, Basis t, Eq (Base t))
                 => [t] -> [[t]] -> (Consistency, [[t]])
checkConsistency lhs rhses = (cons `setRelativised` (rel /= rhses), rel)
  where
    cons = sideConsistency (map basis lhs) (map (map basis) rhses)
    rel  = relativiseSubscripts lhs rhses

sideConsistency :: Eq a => [a] -> [[a]] -> Consistency
sideConsistency xs xss =
  foldr (\ys a -> (sideConsistency1 xs ys) `joinConsistency` a)
    (sideConsistency1 xs (head xss)) (tail xss)

-- Sets all 'relativised' information to True
sideConsistency1 :: Eq a => [a] -> [a] -> Consistency
sideConsistency1 lhs rhs
    | lhs == rhs = Consistent True
    | all (`elem` rhs) lhs && all (`elem` lhs) rhs = Permutation True
    | all (`elem` rhs) lhs = LHSsubset True
    | all (`elem` lhs) rhs = LHSsuperset True
    | otherwise            = Inconsistent

class Basis t where
  type Base t
  basis :: Eq (Base t) => t -> Base t

instance Basis Neighbour where
  type Base Neighbour = String
  basis (Neighbour i _) = i
  basis (Constant _)    = ""

instance Basis (Int, String, Int) where
  type Base (Int, String, Int) = (Int, String)
  basis (a, i, b) = (a, i)

class Relativise t where
  relativiseSubscripts :: [t] -> [[t]] -> [[t]]

instance Relativise Neighbour where
  relativiseSubscripts = relativise

-- affines
instance Relativise (Int, String, Int) where
  relativiseSubscripts lhs rhses = foldr relativiseRHS rhses lhs
    where
      relativiseRHS (a, i, b) rhses = map (map (relativiseBy a i b)) rhses
      relativiseBy a i b (c, j, d) | i == j && a == c = (a, i, d - b)
      relativiseBy _ _ _ x = x

-- ## Classification on subscripts
data Class = Subscript | Affine [[(Int, String, Int)]] | Neigh [[Neighbour]]

classifyIxs :: FAD.InductionVarMapByASTBlock
           -> [[F.Index (FA.Analysis A)]]
           -> Class
classifyIxs ivs ixs =
  case mapM (neighbourIndex ivs) ixs of
    Nothing ->
      case mapM (affineIndex ivs) ixs of
        Nothing -> Subscript
        Just afs -> Affine afs
    Just n -> Neigh n

affineIndex :: FAD.InductionVarMapByASTBlock
            -> [F.Index (FA.Analysis Annotation)]
            -> Maybe [(Int, String, Int)]
affineIndex ivs ix = mapM (ixToAffine ivs) ix

ixToAffine ::  FAD.InductionVarMapByASTBlock
            -> (F.Index (FA.Analysis Annotation))
            -> Maybe (Int, String, Int)
ixToAffine ivmap f@(F.IxSingle _ _ _ exp) =
    matchAffine ivsList exp
  where
    insl = FA.insLabel . F.getAnnotation $ f
    insl' = fromJust insl
    ivsList = S.toList $ fromMaybe S.empty $ IM.lookup insl' ivmap


matchAffine :: [Variable]
            -> F.Expression (FA.Analysis Annotation)
            -> Maybe (Int, String, Int)

-- Allow something of the form a*i or i*a
matchAffine ivs e | matchMult ivs e /= Nothing =
  matchMult ivs e >>= (\(a, i) -> return (a, i, 0))

matchAffine ivs (F.ExpBinary _ _ F.Addition e e') = do
      ((matchMult ivs e) >>= (\(a, i) -> matchConst e' >>= \b -> return (a, i, b)))
  <+> ((matchConst e) >>= (\b -> matchMult ivs e' >>= \(a, i) -> return (a, i, b)))

matchAffine ivs (F.ExpBinary _ _ F.Subtraction e e') =
      ((matchMult ivs e) >>= (\(a, i) -> matchConst e' >>= \b -> return (a, i, -b)))
  <+> ((matchConst e) >>= (\b -> matchMult ivs e' >>= \(a, i) -> return (-a, i, b)))

-- Allow a bare constant, since `matchAffine` is called
-- as part of `affineIndex`, which is only ever called after `neighbourIndex`.
-- This accounts for indices which are a mixture of affine and neighbour and constant
matchAffine ivs e = do
  c <- matchConst e
  return (0, "", c)

(<+>) :: Maybe a -> Maybe a -> Maybe a
Nothing <+> Just a  = Just a
Just a <+> Nothing  = Just a
Nothing <+> Nothing = Nothing
Just a <+> Just b   = Just b

matchMult :: [Variable]
          -> F.Expression (FA.Analysis Annotation)
          -> Maybe (Int, String)
matchMult ivs (F.ExpBinary _ _ F.Multiplication
                 e@(F.ExpValue _ _ (F.ValVariable _))
                   (F.ExpValue _ _ (F.ValInteger a)))
    | FA.varName e `elem` ivs = Just (read a, FA.varName e)

matchMult ivs (F.ExpBinary _ _ F.Multiplication
                  (F.ExpValue _ _ (F.ValInteger a))
                e@(F.ExpValue _ _ (F.ValVariable _)))
    | FA.varName e `elem` ivs = Just (read a, FA.varName e)

-- Allow a bare induction variable, since `matchAffine` is called
-- as part of `affineIndex`, which is only ever called after `neighbourIndex`.
-- This accounts for indices which are a mixture of affine and neighbour
matchMult ivs e@(F.ExpValue _ _ (F.ValVariable {}))
    | FA.varName e `elem` ivs = Just (1, FA.varName e)

matchMult ivs _ = Nothing

matchConst :: F.Expression (FA.Analysis A)
           -> Maybe Int
matchConst (F.ExpValue _ _ (F.ValInteger val)) = Just $ read val
matchConst _                                   = Nothing

-- Work out with the subscript representation comprises of all 'bare' induction
-- variables
hasConstants :: Subscripts t => [t] -> HasConstants
hasConstants = boolToHasConstants . hasConstantsFlag

class Subscripts t where
  allIVs :: [t] -> Bool
  hasConstantsFlag :: [t] -> Bool

instance Subscripts a => Subscripts [a] where
  allIVs       = and . map allIVs
  hasConstantsFlag = or  . map hasConstantsFlag

instance Subscripts (Int, String, Int) where
  allIVs [] = True
  allIVs ((1, i, 0):xs) = allIVs xs
  allIVs _  = False

  hasConstantsFlag [] = False
  hasConstantsFlag ((0, i, 0):xs) = True
  hasConstantsFlag (_:xs) = hasConstantsFlag xs

instance Subscripts Neighbour where
  allIVs [] = True
  allIVs ((Neighbour i 0):xs) = allIVs xs
  allIVs _  = False

  hasConstantsFlag [] = False
  hasConstantsFlag ((Constant _):xs) = True
  hasConstantsFlag (_:xs) = hasConstantsFlag xs