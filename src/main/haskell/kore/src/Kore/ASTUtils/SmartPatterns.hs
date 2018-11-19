{-|
Module      : Data.Kore.ASTUtils.SmartPatterns
Description : Smart patterns for the `PurePattern` AST
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Kore.ASTUtils.SmartPatterns
    ( -- * Pattern synonyms
      pattern And_
    , pattern App_
    , pattern Bottom_
    , pattern Ceil_
    , pattern DV_
    , pattern Equals_
    , pattern Exists_
    , pattern Floor_
    , pattern Forall_
    , pattern Iff_
    , pattern Implies_
    , pattern In_
    , pattern Next_
    , pattern Not_
    , pattern Or_
    , pattern Rewrites_
    , pattern Top_
    , pattern Var_
    , pattern V
    , pattern StringLiteral_
    , pattern CharLiteral_
    )
  where

import Data.Functor.Foldable
       ( Fix (..) )

import Kore.AST.Common
import Kore.AST.MetaOrObject

pattern And_
    :: Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern App_
    :: SymbolOrAlias level
    -> [PureMLPattern level dom var]
    -> PureMLPattern level dom var

pattern Bottom_
    :: Sort level
    -> PureMLPattern level dom var

pattern Ceil_
    :: Sort level
    -> Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern DV_
  :: () => (level ~ Object) =>
     Sort level
  -> dom (PureMLPattern level dom var)
  -> PureMLPattern level dom var

pattern Equals_
    :: Sort level
    -> Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Exists_
    :: Sort level
    -> var level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Floor_
    :: Sort level
    -> Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Forall_
    :: Sort level
    -> var level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Iff_
    :: Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Implies_
    :: Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern In_
    :: Sort level
    -> Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Next_
    :: () => (level ~ Object) =>
       Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Not_
    :: Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Or_
    :: Sort level
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var
    -> PureMLPattern level dom var

pattern Rewrites_
  :: () => (level ~ Object) =>
     Sort level
  -> PureMLPattern level dom var
  -> PureMLPattern level dom var
  -> PureMLPattern level dom var

pattern Top_
    :: Sort level
    -> PureMLPattern level dom var

pattern Var_
    :: var level
    -> PureMLPattern level dom var

pattern StringLiteral_
  :: () => (level ~ Meta)
  => String
  -> PureMLPattern level dom var

pattern CharLiteral_
  :: () => (level ~ Meta)
  => Char
  -> PureMLPattern level dom var

-- No way to make multiline pragma?
-- NOTE: If you add a case to the AST type, add another synonym here.
{-# COMPLETE And_, App_, Bottom_, Ceil_, DV_, Equals_, Exists_, Floor_, Forall_, Iff_, Implies_, In_, Next_, Not_, Or_, Rewrites_, Top_, Var_, StringLiteral_, CharLiteral_ #-}

pattern And_          s2   a b = Fix (AndPattern (And s2 a b))
pattern App_ h c               = Fix (ApplicationPattern (Application h c))
pattern Bottom_       s2       = Fix (BottomPattern (Bottom s2))
pattern Ceil_      s1 s2   a   = Fix (CeilPattern (Ceil s1 s2 a))
pattern DV_           s2   a   = Fix (DomainValuePattern (DomainValue s2 a))
pattern Equals_    s1 s2   a b = Fix (EqualsPattern (Equals s1 s2 a b))
pattern Exists_       s2 v a   = Fix (ExistsPattern (Exists s2 v a))
pattern Floor_     s1 s2   a   = Fix (FloorPattern (Floor s1 s2 a))
pattern Forall_       s2 v a   = Fix (ForallPattern (Forall s2 v a))
pattern Iff_          s2   a b = Fix (IffPattern (Iff s2 a b))
pattern Implies_      s2   a b = Fix (ImpliesPattern (Implies s2 a b))
pattern In_        s1 s2   a b = Fix (InPattern (In s1 s2 a b))
pattern Next_         s2   a   = Fix (NextPattern (Next s2 a))
pattern Not_          s2   a   = Fix (NotPattern (Not s2 a))
pattern Or_           s2   a b = Fix (OrPattern (Or s2 a b))
pattern Rewrites_     s2   a b = Fix (RewritesPattern (Rewrites s2 a b))
pattern Top_          s2       = Fix (TopPattern (Top s2))
pattern Var_             v     = Fix (VariablePattern v)

pattern V :: var level -> PureMLPattern level dom var
pattern V x = Var_ x

pattern StringLiteral_ s = Fix (StringLiteralPattern (StringLiteral s))
pattern CharLiteral_   c = Fix (CharLiteralPattern   (CharLiteral c))
