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
    ( alphaCompare
    ) where

import Data.List

import Kore.AST.Common
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns

alphaCompare e1 e2 = go [] [] e1 e2

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
        && or (zipWith (go ctx1 ctx2) c1 c2)
    (Var_ v1, Var_ v2) -> 
        elemIndex v1 ctx1 == elemIndex v2 ctx2
    _ -> False