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
import Data.Foldable
import Data.Maybe
import Results

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

matchMult ivs _ = Nothing

matchConst :: [Variable]
           -> F.Expression (FA.Analysis Annotation)
           -> Maybe Int
matchConst ivs (F.ExpValue _ _ (F.ValInteger val)) = Just $ read val
matchConst ivs _                                   = Nothing

consistentIV :: Class -> [Class] -> Maybe (Either [String] [(Int, String)])
consistentIV lhs rhses = undefined



consistentAffineRHS rhses = do
    foldr1M (\r x -> sequence $ zipWith affineCmp r x) rhses
affineCmp (a, i, _) (a', i', b') | a == a' && i == i' = Just (a', i', b')

allAffine :: [Class] -> Maybe [[(Int, String, Int)]]
allAffine [] = Nothing
allAffine (Affine is : as) = allAffine as >>= (\as' -> Just (is : as'))

foldr1M f (x:xs) = foldrM f x xs