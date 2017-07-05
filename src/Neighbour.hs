{-# LANGUAGE GADTs #-}

-- Various helpers for manipulating the 'Neighbour' data type and analysisng
-- the shape and other spatial properties of groups of neighbours

module Neighbour where

import Results

import Data.List
import Camfort.Helpers.Vec hiding (toList)
import Camfort.Specification.Stencils.Syntax
import Camfort.Specification.Stencils.Generate
import Camfort.Specification.Stencils.InferenceBackend
import Camfort.Specification.Stencils.DenotationalSemantics
import Camfort.Specification.Stencils.InferenceFrontend
import Data.Maybe


shapeAndPosition :: [[Neighbour]] -> (Shape, Position)
shapeAndPosition ivs =
  case mapM (mapM neighbourToOffset) ivs of
    Nothing -> (Other, Elsewhere)
    Just intIvs ->
      case fromLists intIvs of
        VL intIvs ->
            case regions of
              [x] -> (Orthotope, positioning)
              xs  -> (SumOfOrthotope, positioning)
          where
            regions = inferMinimalVectorRegions intIvs
            positioning = if any originVec intIvs
                          then OverOrigin
                          else intervalsToPosition regions

intervalsToPosition :: [Span (Vec n Int)] -> Position
intervalsToPosition vs =
    fromMaybe OverOrigin
  . foldVecMeet
  . foldr1 meetVecPosition
  . map (fmap positionInterval . transposeVecInterval)
  $ vs
reportEmptyError [] = error "intervalToPosition []"
reportEmptyError xs = xs

originVec :: Vec n Int -> Bool
originVec Nil         = True
originVec (Cons 0 vs) = originVec vs
originVec _           = False

originSpan :: Vec n Int -> Vec n Int -> Bool
originSpan Nil Nil                 = True
originSpan (Cons 0 xs) (Cons 0 ys) = originSpan xs ys
originSpan _ _                     = False

toList :: Vec n a -> [a]
toList Nil = []
toList (Cons x xs) = x : toList xs

foldVecMeet :: Vec n (Maybe Position) -> Maybe Position
foldVecMeet Nil = Just OverOrigin
foldVecMeet (Cons p Nil) = p
foldVecMeet (Cons p vs)  = do
  pos <- p
  pos' <- foldVecMeet vs
  return (pos `meetPositionAlt` pos')

meetPositionAlt :: Position -> Position -> Position
meetPositionAlt OverOrigin     OverOrigin     = OverOrigin
meetPositionAlt StraddleOrigin StraddleOrigin = StraddleOrigin
meetPositionAlt Elsewhere      _              = Elsewhere
meetPositionAlt _              Elsewhere      = Elsewhere
meetPositionAlt _              _              = StraddleOrigin

meetPosition :: Position -> Position -> Position
meetPosition OverOrigin     OverOrigin     = OverOrigin
meetPosition OverOrigin     _              = StraddleOrigin
meetPosition _              OverOrigin     = StraddleOrigin
meetPosition StraddleOrigin StraddleOrigin = StraddleOrigin
meetPosition StraddleOrigin _              = StraddleOrigin
meetPosition _     StraddleOrigin          = StraddleOrigin
meetPosition _              _              = Elsewhere

meetVecPosition :: Vec n (Maybe Position)
                -> Vec n (Maybe Position)
                -> Vec n (Maybe Position)
meetVecPosition Nil Nil = Nil
meetVecPosition (Cons p vs) (Cons q vs') =
    Cons (meetLift p q)
         (meetVecPosition vs vs')
 where
   meetLift Nothing Nothing = Nothing
   meetLift (Just a) Nothing = Just a
   meetLift Nothing (Just b) = Just b
   meetLift (Just a) (Just b) = Just $ meetPosition a b

-- Penelope 15/04/2017 ufkvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv,.

transposeVecInterval :: Span (Vec n Int) -> Vec n (Span Int)
transposeVecInterval (Nil, Nil) = Nil
transposeVecInterval (Cons l ls, Cons u us) = Cons (l, u) intervalVec
  where
    intervalVec = transposeVecInterval (ls, us)

positionInterval :: (Int, Int) -> Maybe Position
positionInterval (l, u)
  | l == -absoluteRep || u == absoluteRep = Nothing
  | l <= 0 && u >= 0                      = Just OverOrigin
  | l < 0  && u == (-1)                   = Just StraddleOrigin
  | l == 1 && u > 0                       = Just StraddleOrigin
  | otherwise                             = Just Elsewhere

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
hasNeighbouringIx ns nss
  = foldr ((||) . neighbouringIxs ns) False nss

-- Given two indices, find out if they are (rectilinear) neighbours
neighbouringIxs :: [Neighbour] -> [Neighbour] -> Bool
neighbouringIxs [] [] = True
neighbouringIxs (x : xs) (y : ys) | x == y = neighbouringIxs xs ys
neighbouringIxs (Neighbour v o : xs) (Neighbour v' o' : ys)
  | v == v' && abs (o - o') == 1 && xs == ys = True
neighbouringIxs _ _ = False

-- Predicate on whether an index is at the origin
isOrigin :: [Neighbour] -> Bool
isOrigin nixs = all (\i -> case i of Neighbour _ 0 -> True; _ -> False) nixs

-- Predicate on whether an index is rectilinearly next to the origin
nextToOrigin :: [Neighbour] -> Bool
nextToOrigin [] = True
nextToOrigin (Neighbour _ 1:nixs) = isOrigin nixs
nextToOrigin (Neighbour _ (-1):nixs) = isOrigin nixs
nextToOrigin (Neighbour _ 0:nixs) = nextToOrigin nixs
nextToOrigin _ = False

-- Treat an affine index as a neighbour index
affineToNeighbour :: (Int, String, Int) -> Neighbour
affineToNeighbour (a, i, b) = Neighbour (show a ++ "*" ++ i) b

-- Extract the variable from a neighbour
neighbourVar :: Neighbour -> Maybe String
neighbourVar (Neighbour v _) = Just v
neighbourVar (Constant _)    = Just ""
neighbourVar _               = Nothing
