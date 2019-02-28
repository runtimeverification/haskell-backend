{-|
Module      : Data.Kore.ASTUtils.SmartPatterns
Description : Smart patterns for the `PurePattern` AST
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

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

import qualified Data.Functor.Foldable as Recursive
import           Data.Text
                 ( Text )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Pure
import           Kore.Domain.Class

pattern And_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern App_
    :: Functor dom
    => SymbolOrAlias level
    -> [PurePattern level dom var (Annotation.Null level)]
    -> PurePattern level dom var (Annotation.Null level)

pattern Bottom_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)

pattern Ceil_
    :: Functor dom
    => Sort level
    -> Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern DV_
  :: Domain dom => (level ~ Object)
  => dom (PurePattern level dom var (Annotation.Null level))
  -> PurePattern level dom var (Annotation.Null level)

pattern Equals_
    :: Functor dom
    => Sort level
    -> Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Exists_
    :: Functor dom
    => Sort level
    -> var level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Floor_
    :: Functor dom
    => Sort level
    -> Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Forall_
    :: Functor dom
    => Sort level
    -> var level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Iff_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Implies_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern In_
    :: Functor dom
    => Sort level
    -> Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Next_
    :: Functor dom => (level ~ Object) =>
       Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Not_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Or_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)
    -> PurePattern level dom var (Annotation.Null level)

pattern Rewrites_
  :: Functor dom => (level ~ Object) =>
     Sort level
  -> PurePattern level dom var (Annotation.Null level)
  -> PurePattern level dom var (Annotation.Null level)
  -> PurePattern level dom var (Annotation.Null level)

pattern Top_
    :: Functor dom
    => Sort level
    -> PurePattern level dom var (Annotation.Null level)

pattern Var_
    :: Functor dom
    => var level
    -> PurePattern level dom var (Annotation.Null level)

pattern StringLiteral_
  :: Functor dom => (level ~ Meta)
  => Text
  -> PurePattern level dom var (Annotation.Null level)

pattern CharLiteral_
  :: Functor dom => (level ~ Meta)
  => Char
  -> PurePattern level dom var (Annotation.Null level)

-- No way to make multiline pragma?
-- NOTE: If you add a case to the AST type, add another synonym here.
{-# COMPLETE And_, App_, Bottom_, Ceil_, DV_, Equals_, Exists_, Floor_, Forall_, Iff_, Implies_, In_, Next_, Not_, Or_, Rewrites_, Top_, Var_, StringLiteral_, CharLiteral_ #-}

pattern And_ andSort andFirst andSecond <-
    (Recursive.project -> _ :< AndPattern And { andSort, andFirst, andSecond })
  where
    And_ andSort andFirst andSecond =
        (asPurePattern . (:<) mempty . AndPattern)
            And { andSort, andFirst, andSecond }

pattern App_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplicationPattern Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )
  where
    App_ applicationSymbolOrAlias applicationChildren =
        (asPurePattern . (:<) mempty . ApplicationPattern)
            Application { applicationSymbolOrAlias, applicationChildren }

pattern Bottom_ bottomSort <-
    (Recursive.project -> _ :< BottomPattern Bottom { bottomSort })
  where
    Bottom_ bottomSort =
        (asPurePattern . (:<) mempty . BottomPattern) Bottom { bottomSort }

pattern Ceil_ ceilOperandSort ceilResultSort ceilChild <-
    (Recursive.project ->
        _ :< CeilPattern Ceil { ceilOperandSort, ceilResultSort, ceilChild }
    )
  where
    Ceil_ ceilOperandSort ceilResultSort ceilChild =
        (asPurePattern . (:<) mempty . CeilPattern)
            Ceil { ceilOperandSort, ceilResultSort, ceilChild }

pattern DV_ domainValue <-
    (Recursive.project -> _ :< DomainValuePattern domainValue)
  where
    DV_ domainValue = asPurePattern (mempty :< DomainValuePattern domainValue)

pattern Equals_ equalsOperandSort equalsResultSort equalsFirst equalsSecond <-
    (Recursive.project ->
        _ :< EqualsPattern Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
    )
  where
    Equals_ equalsOperandSort equalsResultSort equalsFirst equalsSecond =
        (asPurePattern . (:<) mempty . EqualsPattern)
            Equals
                { equalsOperandSort
                , equalsResultSort
                , equalsFirst
                , equalsSecond
                }

pattern Exists_ existsSort existsVariable existsChild <-
    (Recursive.project ->
        _ :< ExistsPattern Exists { existsSort, existsVariable, existsChild }
    )
  where
    Exists_ existsSort existsVariable existsChild =
        (asPurePattern . (:<) mempty . ExistsPattern)
            Exists { existsSort, existsVariable, existsChild }

pattern Floor_ floorOperandSort floorResultSort floorChild <-
    (Recursive.project ->
        _ :< FloorPattern Floor
            { floorOperandSort
            , floorResultSort
            , floorChild
            }
    )
  where
    Floor_ floorOperandSort floorResultSort floorChild =
        (asPurePattern . (:<) mempty . FloorPattern)
            Floor { floorOperandSort, floorResultSort, floorChild }

pattern Forall_ forallSort forallVariable forallChild <-
    (Recursive.project ->
        _ :< ForallPattern Forall { forallSort, forallVariable, forallChild }
    )
  where
    Forall_ forallSort forallVariable forallChild =
        (asPurePattern . (:<) mempty . ForallPattern)
            Forall { forallSort, forallVariable, forallChild }

pattern Iff_ iffSort iffFirst iffSecond <-
    (Recursive.project ->
        _ :< IffPattern Iff { iffSort, iffFirst, iffSecond }
    )
  where
    Iff_ iffSort iffFirst iffSecond =
        (asPurePattern . (:<) mempty . IffPattern)
            Iff { iffSort, iffFirst, iffSecond }

pattern Implies_ impliesSort impliesFirst impliesSecond <-
    (Recursive.project ->
        _ :< ImpliesPattern Implies { impliesSort, impliesFirst, impliesSecond }
    )
  where
    Implies_ impliesSort impliesFirst impliesSecond =
        (asPurePattern . (:<) mempty . ImpliesPattern)
            Implies { impliesSort, impliesFirst, impliesSecond }

pattern In_ inOperandSort inResultSort inFirst inSecond <-
    (Recursive.project ->
        _ :< InPattern In
            { inOperandSort
            , inResultSort
            , inContainedChild = inFirst
            , inContainingChild = inSecond
            }
    )
  where
    In_ inOperandSort inResultSort inFirst inSecond =
        (asPurePattern . (:<) mempty . InPattern)
            In
                { inOperandSort
                , inResultSort
                , inContainedChild = inFirst
                , inContainingChild = inSecond
                }

pattern Next_ nextSort nextChild <-
    (Recursive.project ->
        _ :< NextPattern Next { nextSort, nextChild })
  where
    Next_ nextSort nextChild =
        (asPurePattern . (:<) mempty . NextPattern) Next { nextSort, nextChild }

pattern Not_ notSort notChild <-
    (Recursive.project ->
        _ :< NotPattern Not { notSort, notChild })
  where
    Not_ notSort notChild =
        (asPurePattern . (:<) mempty . NotPattern) Not { notSort, notChild }

pattern Or_ orSort orFirst orSecond <-
    (Recursive.project -> _ :< OrPattern Or { orSort, orFirst, orSecond })
  where
    Or_ orSort orFirst orSecond =
        (asPurePattern . (:<) mempty . OrPattern)
            Or { orSort, orFirst, orSecond }

pattern Rewrites_ rewritesSort rewritesFirst rewritesSecond <-
    (Recursive.project ->
        _ :< RewritesPattern Rewrites
            { rewritesSort
            , rewritesFirst
            , rewritesSecond
            }
    )
  where
    Rewrites_ rewritesSort rewritesFirst rewritesSecond =
        (asPurePattern . (:<) mempty . RewritesPattern)
            Rewrites { rewritesSort, rewritesFirst, rewritesSecond }

pattern Top_ topSort <-
    (Recursive.project -> _ :< TopPattern Top { topSort })
  where
    Top_ topSort =
        (asPurePattern . (:<) mempty . TopPattern) Top { topSort }

pattern Var_ variable <-
    (Recursive.project -> _ :< VariablePattern variable)
  where
    Var_ variable =
        (asPurePattern . (:<) mempty) (VariablePattern variable)

pattern V
    :: Functor dom
    => var level
    -> PurePattern level dom var (Annotation.Null level)
pattern V x = Var_ x

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralPattern (StringLiteral str))
  where
    StringLiteral_ str =
        (asPurePattern . (:<) mempty) (StringLiteralPattern (StringLiteral str))

pattern CharLiteral_ char <-
    (Recursive.project -> _ :< CharLiteralPattern (CharLiteral char))
  where
    CharLiteral_ char =
        (asPurePattern . (:<) mempty) (CharLiteralPattern (CharLiteral char))
