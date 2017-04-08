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
import Data.Maybe
import Results


-- Main function for classifying array statements
classify :: FAD.InductionVarMapByASTBlock
         -> F.Expression (FA.Analysis A)
         -> M.Map Variable [[F.Index (FA.Analysis A)]]
         -> (String, Cat, Result)
classify ivs lhs rhses = (debug, cat, undefined)
  where
    debug = ""
    result = undefined
    cat = (formLHS, formRHS, consistency)
    formLHS = undefined
    formRHS = undefined
    consistency = undefined
    lhsClassifiers =
      case isArraySubscript lhs of
        Nothing   -> Vars
        Just subs -> undefined -- classifyIx ivs subs

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

matchAffine ivs (F.ExpBinary _ _ F.Addition e e') =
      ((matchMult ivs e) >>= (\(a, i) -> matchConst ivs e' >>= \b -> return (a, i, b)))
  <+> ((matchConst ivs e') >>= (\b -> matchMult ivs e >>= \(a, i) -> return (a, i, b)))

matchAffine ivs (F.ExpBinary _ _ F.Subtraction e e') =
      ((matchMult ivs e) >>= (\(a, i) -> matchConst ivs e' >>= \b -> return (a, i, -b)))
  <+> ((matchConst ivs e') >>= (\b -> matchMult ivs e >>= \(a, i) -> return (-a, i, b)))

matchAffine _ e = Nothing

(<+>) :: Maybe a -> Maybe a -> Maybe a
Nothing <+> Just a  = Just a
Just a <+> Nothing  = Just a
Nothing <+> Nothing = Nothing
Just a <+> Just _   = Nothing

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

matchConst :: [Variable]
           -> F.Expression (FA.Analysis A)
           -> Maybe Int
matchConst ivs (F.ExpValue _ _ (F.ValInteger val)) = Just $ read val
matchConst ivs _                                   = Nothing

classifyIx :: FAD.InductionVarMapByASTBlock
           -> [F.Index (FA.Analysis A)]
           -> Class
classifyIx ivs ix =
  case neighbourIndex ivs ix of
    Nothing ->
      case affineIndex ivs ix of
        Nothing -> Subscript
        Just afs -> Affine afs
    Just n -> Neigh n


neighbourConsistency :: Eq a => [a] -> [a] -> (Relativised -> Consistency)
neighbourConsistency lhs rhs
    | lhs == rhs = Consistent
    | all (`elem` rhs) lhs && all (`elem` lhs) rhs = Permutation
    | all (`elem` rhs) lhs = LHSsuperset
    | all (`elem` lhs) rhs = LHSsubset
    | otherwise            = \_ -> Inconsistent

consistentNeighbours :: [Class] -> Maybe [String]
consistentNeighbours ixs = do
   neighbourReps <- allNeighbours ixs
   foldr1M eqW neighbourReps

eqW :: Eq a => a -> a -> Maybe a
eqW x y | x == y = Just x
eqW _ _          = Nothing

allNeighbours :: [Class] -> Maybe [[String]]
allNeighbours [] = error $ "Non-empty classification, shouldn't happen"
allNeighbours ((Neigh ns):nss) = do
    vs <- mapM neighbourVar ns
    nss' <- allNeighbours nss
    return (vs : nss')

neighbourVar :: Neighbour -> Maybe String
neighbourVar (Neighbour v _) = Just v
neighbourVar (Constant _)    = Just ""
neighbourVar _               = Nothing

-- consistentAffines - takes a list of index classifiers
--    returns Just of a list of pairs representing scalar mults. of IVs
--      if all indices are affine with the same basis
--    otherwise Nothing
consistentAffines :: [Class] -> Maybe [(Int, String)]
consistentAffines ixs = do
    affineReps <- allAffine ixs
    consistents <- foldr1M (\r x -> sequence $ zipWith affineCmp r x) affineReps
    return $ map (\(a, i, _) -> (a, i)) consistents
affineCmp (a, i, _) (a', i', b') | a == a' && i == i' = Just (a', i', b')

allAffine :: [Class] -> Maybe [[(Int, String, Int)]]
allAffine [] = error $ "Non-empty classification, shouldn't happen"
allAffine (Affine is : as) = allAffine as >>= (\as' -> Just (is : as'))

foldr1M f (x:xs) = foldrM f x xs