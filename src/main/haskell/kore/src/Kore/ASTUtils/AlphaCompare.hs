{-|
Module      : Kore.ASTUtils.AlphaCompare
Description : Compare
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.ASTUtils.AlphaCompare
    ( alphaEq
    ) where

import           Data.List
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain

-- alphaEq compares terms modulo renaming of bound variables
-- bound variables are variables in the first position of a
-- Forall or Exists constructor that we encoutner as we recurse
-- down the tree.

-- As we recurse down we collect these variables in the order we
-- see them in `ctx1` and `ctx2`. Then comparing `elemIndex v1/2 ctx1/2`
-- is equivalent to comparing the de Bruijn indices of v1 and v2.

-- This handles shadowing correctly, since `elemIndex elem` returns the
-- lowest index if there are multiple occurences of `elem`.

alphaEq
    ::  forall level var.
        ( MetaOrObject level
        , Eq (var level)
        , Ord (var level)
        , Eq (var Meta)
        , Ord (var Meta)
        , Eq (var Object)
        , Ord (var Object)
        )
    => PureMLPattern level Domain.Builtin var
    -> PureMLPattern level Domain.Builtin var
    -> Bool
alphaEq e1' e2' = go [] [] e1' e2'

go
    ::  forall level var.
        ( MetaOrObject level
        , Eq (var level)
        , Ord (var level)
        , Eq (var Meta)
        , Ord (var Meta)
        , Eq (var Object)
        , Ord (var Object)
        )
    => [var level]
    -> [var level]
    -> PureMLPattern level Domain.Builtin var
    -> PureMLPattern level Domain.Builtin var
    -> Bool
go ctx1 ctx2 e1 e2 = case (e1, e2) of
    (And_ s1 a1 b1, And_ s2 a2 b2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Bottom_ s1, Bottom_ s2) ->
        s1 == s2
    (Ceil_ s1 ss1 a1, Ceil_ s2 ss2 a2) ->
        s1 == s2
        && ss1 == ss2
        && go ctx1 ctx2 a1 a2
    (Equals_ s1 ss1 a1 b1, Equals_ s2 ss2 a2 b2) ->
        s1 == s2
        && ss1 == ss2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Exists_ s1 v1 a1, Exists_ s2 v2 a2) ->
        s1 == s2
        && go (v1 : ctx1) (v2 : ctx2) a1 a2
    (Forall_ s1 v1 a1, Forall_ s2 v2 a2) ->
        s1 == s2
        && go (v1 : ctx1) (v2 : ctx2) a1 a2
    (Floor_ s1 ss1 a1, Floor_ s2 ss2 a2) ->
        s1 == s2
        && ss1 == ss2
        && go ctx1 ctx2 a1 a2
    (Iff_ s1 a1 b1, Iff_ s2 a2 b2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Implies_ s1 a1 b1, Implies_ s2 a2 b2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (In_ s1 ss1 a1 b1, In_ s2 ss2 a2 b2) ->
        s1 == s2
        && ss1 == ss2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Next_ s1 a1, Next_ s2 a2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
    (Not_ s1 a1, Not_ s2 a2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
    (Or_ s1 a1 b1, Or_ s2 a2 b2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Rewrites_ s1 a1 b1, Rewrites_ s2 a2 b2) ->
        s1 == s2
        && go ctx1 ctx2 a1 a2
        && go ctx1 ctx2 b1 b2
    (Top_ s1, Top_ s2) ->
        s1 == s2
    (StringLiteral_ s1, StringLiteral_ s2) ->
        s1 == s2
    (CharLiteral_ c1, CharLiteral_ c2) ->
        c1 == c2
    (App_ h1 c1, App_ h2 c2) ->
        h1 == h2
        && and (zipWith (go ctx1 ctx2) c1 c2)
    (Var_ v1, Var_ v2) ->
        case elemIndex v1 ctx1 of
            Just i -> (Just i) == elemIndex v2 ctx2
            Nothing -> v1 == v2
    (DV_ s1 dv1, DV_ s2 dv2) ->
        s1 == s2
        && compareDV ctx1 ctx2 dv1 dv2
    _ -> False

compareDV
    ::  forall level var.
        ( MetaOrObject level
        , Eq (var level)
        , Ord (var level)
        , Eq (var Meta)
        , Ord (var Meta)
        , Eq (var Object)
        , Ord (var Object)
        )
    => [var level]
    -> [var level]
    -> Domain.Builtin (PureMLPattern level Domain.Builtin var)
    -> Domain.Builtin (PureMLPattern level Domain.Builtin var)
    -> Bool
compareDV ctx1 ctx2 dv1 dv2 = case (dv1, dv2) of
    (Domain.BuiltinList l1, Domain.BuiltinList l2) ->
        and $ Seq.zipWith (go ctx1 ctx2) l1 l2
    (Domain.BuiltinSet s1, Domain.BuiltinSet s2) ->
        and $ zipWith
            (go [] [])
            (sort $ Set.toList s1)
            (sort $ Set.toList s2)
    (Domain.BuiltinMap m1, Domain.BuiltinMap m2) ->
        and $ zipWith (go ctx1 ctx2)
            (map snd $ sort $ Map.toList m1)
            (map snd $ sort $ Map.toList m2)
    (Domain.BuiltinPattern p1, Domain.BuiltinPattern p2) ->
        go [] [] (castVoidDomainValues p1) (castVoidDomainValues p2)
    _ -> False
