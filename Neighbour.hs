{-# LANGUAGE GADTs#-}

-- Various helpers for manipulating the 'Neighbour' data type and analysisng
-- the shape and other spatial properties of groups of neighbours

module Neighbour where

import Results

import Data.List
import Camfort.Helpers.Vec
import Camfort.Specification.Stencils.Syntax
import Camfort.Specification.Stencils.InferenceBackend
import Camfort.Specification.Stencils.InferenceFrontend



shapeAndPosition :: [[Neighbour]] -> (Shape, Position)
shapeAndPosition ivs =
  case mapM (mapM neighbourToOffset) ivs of
    Nothing -> (Other, Elsewhere)
    Just intIvs ->
      case fromLists intIvs of
        VL intIvs ->
          classifyIntervalRegions (inferMinimalVectorRegions intIvs)

classifyIntervalRegions :: [Span (Vec n Int)] -> (Shape, Position)
classifyIntervalRegions [] = error "classifyIntervalRegions []"
classifyIntervalRegions [x] =
    (Orthotope, intervalToPosition x)
classifyIntervalRegions xs =
    (SumOfOrthotope, foldr1 joinPosition . map intervalToPosition $ xs)

intervalToPosition = foldr1 joinPosition . reportEmptyError . map positionInterval . toList . transposeVecInterval
reportEmptyError [] = error "intervalToPosition []"
reportEmptyError xs = xs

toList :: Vec n a -> [a]
toList Nil = []
toList (Cons x xs) = x : (toList xs)

transposeVecInterval :: Span (Vec n Int) -> Vec n (Span Int)
transposeVecInterval (Nil, Nil) = Nil
transposeVecInterval (Cons l ls, Cons u us) = Cons (l, u) intervalVec
  where
    intervalVec = transposeVecInterval (ls, us)


positionInterval :: (Int, Int) -> Position
positionInterval (l, u)
  | l == -absoluteRep || u == absoluteRep = OverOrigin
  | l <= 0 && u >= 0                      = OverOrigin
  | l < 0  && u == (-1)                   = StraddleOrigin
  | l == 1 && u > 0                       = StraddleOrigin
  | otherwise                             = Elsewhere

-- Contiguous stencil (need not include the origin)
contiguous :: [[Neighbour]] -> Bool
contiguous xs = contiguity' xs
  where
    contiguity' [] = True
    contiguity' [x] = True
    contiguity' (y : ys) | isOrigin y = contiguity' ys
    contiguity' (y : ys) | nextToOrigin y = contiguity' ys
    contiguity' (y : ys) | hasNeighbouringIx y (xs \\ [y]) = contiguity' ys
    contiguity' _ = False

-- Given an index 'ns' and a set of indices 'nss',
-- find if 'ns' has a neighbour in 'nss'
hasNeighbouringIx :: [Neighbour] -> [[Neighbour]] -> Bool
hasNeighbouringIx ns [] = False
hasNeighbouringIx ns (ns' : nss) =
  neighbouringIxs ns ns' || hasNeighbouringIx ns nss

-- Given two indices, find out if they are (rectilinear) neighbours
neighbouringIxs :: [Neighbour] -> [Neighbour] -> Bool
neighbouringIxs [] [] = True
neighbouringIxs (x : xs) (y : ys) | x == y = neighbouringIxs xs ys
neighbouringIxs ((Neighbour v o) : xs) ((Neighbour v' o') : ys)
  | v == v' && abs (o - o') == 1 && xs == ys = True
neighbouringIxs _ _ = False

-- Predicate on whether an index is at the origin
isOrigin :: [Neighbour] -> Bool
isOrigin nixs = all (\i -> case i of Neighbour _ 0 -> True; _ -> False) nixs

-- Predicate on whether an index is rectilinearly next to the origin
nextToOrigin :: [Neighbour] -> Bool
nextToOrigin [] = True
nextToOrigin ((Neighbour _ 1):nixs) = isOrigin nixs
nextToOrigin ((Neighbour _ (-1)):nixs) = isOrigin nixs
nextToOrigin ((Neighbour _ 0):nixs) = nextToOrigin nixs
nextToOrigin _ = False

-- Treat an affine index as a neighbour index
affineToNeighbour :: (Int, String, Int) -> Neighbour
affineToNeighbour (a, i, b) = Neighbour (show a ++ "*" ++ i) b

-- Extract the variable from a neighbour
neighbourVar :: Neighbour -> Maybe String
neighbourVar (Neighbour v _) = Just v
neighbourVar (Constant _)    = Just ""
neighbourVar _               = Nothing
