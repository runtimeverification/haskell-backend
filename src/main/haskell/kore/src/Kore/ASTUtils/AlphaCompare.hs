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

import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Monad.Reader
                 ( Reader, runReader )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import           Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Kore.AST.Pure as Pure
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
    ::  ( MetaOrObject level
        , Eq (var level)
        , Ord (var level)
        , EqMetaOrObject var
        , OrdMetaOrObject var
        )
    => PurePattern level Domain.Builtin var annotation
    -> PurePattern level Domain.Builtin var annotation
    -> Bool
alphaEq e1' e2' = Reader.runReader (alphaEqWorker e1' e2') ([], [])
  where
    project
        :: PurePattern level Domain.Builtin var annotation
        -> Pattern level Domain.Builtin var
            (PurePattern level Domain.Builtin var annotation)
    project = Cofree.tailF . Recursive.project

    alphaEqWorker
        ::  ( Eq (var level)
            , Ord (var level)
            )
        => PurePattern level Domain.Builtin var annotation
        -> PurePattern level Domain.Builtin var annotation
        -> Reader ([var level], [var level]) Bool
    alphaEqWorker e1 e2 =
        case (project e1, project e2) of
            (AndPattern and1, AndPattern and2) -> compareAnd and1 and2
            (ApplicationPattern app1, ApplicationPattern app2) ->
                compareApplication app1 app2
            (BottomPattern bot1, BottomPattern bot2) -> compareBottom bot1 bot2
            (CeilPattern ceil1, CeilPattern ceil2) -> compareCeil ceil1 ceil2
            (CharLiteralPattern lit1, CharLiteralPattern lit2) ->
                compareCharLiteral lit1 lit2
            (DomainValuePattern dv1, DomainValuePattern dv2) ->
                compareDomainValue dv1 dv2
            (EqualsPattern eq1, EqualsPattern eq2) -> compareEquals eq1 eq2
            (ExistsPattern ex1, ExistsPattern ex2) -> compareExists ex1 ex2
            (ForallPattern fa1, ForallPattern fa2) -> compareForall fa1 fa2
            (FloorPattern flr1, FloorPattern flr2) -> compareFloor flr1 flr2
            (IffPattern iff1, IffPattern iff2) -> compareIff iff1 iff2
            (ImpliesPattern imp1, ImpliesPattern imp2) ->
                compareImplies imp1 imp2
            (InPattern in1, InPattern in2) -> compareIn in1 in2
            (NextPattern nxt1, NextPattern nxt2) -> compareNext nxt1 nxt2
            (NotPattern not1, NotPattern not2) -> compareNot not1 not2
            (OrPattern or1, OrPattern or2) -> compareOr or1 or2
            (RewritesPattern rew1, RewritesPattern rew2) ->
                compareRewrites rew1 rew2
            (StringLiteralPattern lit1, StringLiteralPattern lit2) ->
                compareStringLiteral lit1 lit2
            (TopPattern top1, TopPattern top2) -> compareTop top1 top2
            (VariablePattern var1, VariablePattern var2) ->
                compareVariable var1 var2
            _ -> return False

    compareChildren children1 children2 =
        and <$> Reader.zipWithM alphaEqWorker children1 children2

    compareAnd
        And
            { andSort = andSort1
            , andFirst = andFirst1
            , andSecond = andSecond1
            }
        And
            { andSort = andSort2
            , andFirst = andFirst2
            , andSecond = andSecond2
            }
      | andSort1 == andSort2 =
        (&&)
            <$> alphaEqWorker andFirst1 andFirst2
            <*> alphaEqWorker andSecond1 andSecond2
      | otherwise = return False

    compareBottom
        Bottom { bottomSort = bottomSort1 }
        Bottom { bottomSort = bottomSort2 }
      =
        return (bottomSort1 == bottomSort2)

    compareCeil
        Ceil
            { ceilOperandSort = ceilOperandSort1
            , ceilResultSort = ceilResultSort1
            , ceilChild = ceilChild1
            }
        Ceil
            { ceilOperandSort = ceilOperandSort2
            , ceilResultSort = ceilResultSort2
            , ceilChild = ceilChild2
            }
      | sameSort = alphaEqWorker ceilChild1 ceilChild2
      | otherwise = return False
      where
        sameSort =
            ceilOperandSort1 == ceilOperandSort2
            && ceilResultSort1 == ceilResultSort2

    compareEquals
        Equals
            { equalsOperandSort = equalsOperandSort1
            , equalsResultSort = equalsResultSort1
            , equalsFirst = equalsFirst1
            , equalsSecond = equalsSecond1
            }
        Equals
            { equalsOperandSort = equalsOperandSort2
            , equalsResultSort = equalsResultSort2
            , equalsFirst = equalsFirst2
            , equalsSecond = equalsSecond2
            }
      | sameSort =
        (&&)
            <$> alphaEqWorker equalsFirst1 equalsFirst2
            <*> alphaEqWorker equalsSecond1 equalsSecond2
      | otherwise = return False
      where
        sameSort =
            equalsOperandSort1 == equalsOperandSort2
            && equalsResultSort1 == equalsResultSort2

    compareExists
        Exists
            { existsSort = existsSort1
            , existsVariable = existsVariable1
            , existsChild = existsChild1
            }
        Exists
            { existsSort = existsSort2
            , existsVariable = existsVariable2
            , existsChild = existsChild2
            }
      | existsSort1 == existsSort2 =
        Reader.local withBoundVariables
            (alphaEqWorker existsChild1 existsChild2)
      | otherwise = return False
      where
        withBoundVariables (ctx1, ctx2) =
            (existsVariable1 : ctx1, existsVariable2 : ctx2)

    compareForall
        Forall
            { forallSort = forallSort1
            , forallVariable = forallVariable1
            , forallChild = forallChild1
            }
        Forall
            { forallSort = forallSort2
            , forallVariable = forallVariable2
            , forallChild = forallChild2
            }
      | forallSort1 == forallSort2 =
        Reader.local withBoundVariables
            (alphaEqWorker forallChild1 forallChild2)
      | otherwise = return False
      where
        withBoundVariables (ctx1, ctx2) =
            (forallVariable1 : ctx1, forallVariable2 : ctx2)

    compareFloor
        Floor
            { floorOperandSort = floorOperandSort1
            , floorResultSort = floorResultSort1
            , floorChild = floorChild1
            }
        Floor
            { floorOperandSort = floorOperandSort2
            , floorResultSort = floorResultSort2
            , floorChild = floorChild2
            }
      | sameSort = alphaEqWorker floorChild1 floorChild2
      | otherwise = return False
      where
        sameSort =
            floorOperandSort1 == floorOperandSort2
            && floorResultSort1 == floorResultSort2

    compareIff
        Iff
            { iffSort = iffSort1
            , iffFirst = iffFirst1
            , iffSecond = iffSecond1
            }
        Iff
            { iffSort = iffSort2
            , iffFirst = iffFirst2
            , iffSecond = iffSecond2
            }
      | iffSort1 == iffSort2 =
        (&&)
            <$> alphaEqWorker iffFirst1 iffFirst2
            <*> alphaEqWorker iffSecond1 iffSecond2
      | otherwise = return False

    compareImplies
        Implies
            { impliesSort = impliesSort1
            , impliesFirst = impliesFirst1
            , impliesSecond = impliesSecond1
            }
        Implies
            { impliesSort = impliesSort2
            , impliesFirst = impliesFirst2
            , impliesSecond = impliesSecond2
            }
      | impliesSort1 == impliesSort2 =
        (&&)
            <$> alphaEqWorker impliesFirst1 impliesFirst2
            <*> alphaEqWorker impliesSecond1 impliesSecond2
      | otherwise = return False

    compareIn
        In
            { inOperandSort = inOperandSort1
            , inResultSort = inResultSort1
            , inContainedChild = inContainedChild1
            , inContainingChild = inContainingChild1
            }
        In
            { inOperandSort = inOperandSort2
            , inResultSort = inResultSort2
            , inContainedChild = inContainedChild2
            , inContainingChild = inContainingChild2
            }
      | sameSort =
        (&&)
            <$> alphaEqWorker inContainedChild1 inContainedChild2
            <*> alphaEqWorker inContainingChild1 inContainingChild2
      | otherwise = return False
      where
        sameSort =
            inOperandSort1 == inOperandSort2
            && inResultSort1 == inResultSort2

    compareNext
        :: Ord (var level)
        => Next Object (PurePattern level Domain.Builtin var annotation)
        -> Next Object (PurePattern level Domain.Builtin var annotation)
        -> Reader ([var level], [var level]) Bool
    compareNext
        Next
            { nextSort = nextSort1
            , nextChild = nextChild1
            }
        Next
            { nextSort = nextSort2
            , nextChild = nextChild2
            }
      | nextSort1 == nextSort2 = alphaEqWorker nextChild1 nextChild2
      | otherwise = return False

    compareNot
        Not
            { notSort = notSort1
            , notChild = notChild1
            }
        Not
            { notSort = notSort2
            , notChild = notChild2
            }
      | notSort1 == notSort2 = alphaEqWorker notChild1 notChild2
      | otherwise = return False

    compareOr
        Or
            { orSort = orSort1
            , orFirst = orFirst1
            , orSecond = orSecond1
            }
        Or
            { orSort = orSort2
            , orFirst = orFirst2
            , orSecond = orSecond2
            }
      | orSort1 == orSort2 =
        (&&)
            <$> alphaEqWorker orFirst1 orFirst2
            <*> alphaEqWorker orSecond1 orSecond2
      | otherwise = return False

    compareRewrites
        :: Ord (var level)
        => Rewrites Object (PurePattern level Domain.Builtin var annotation)
        -> Rewrites Object (PurePattern level Domain.Builtin var annotation)
        -> Reader ([var level], [var level]) Bool
    compareRewrites
        Rewrites
            { rewritesSort = rewritesSort1
            , rewritesFirst = rewritesFirst1
            , rewritesSecond = rewritesSecond1
            }
        Rewrites
            { rewritesSort = rewritesSort2
            , rewritesFirst = rewritesFirst2
            , rewritesSecond = rewritesSecond2
            }
      | rewritesSort1 == rewritesSort2 =
        (&&)
            <$> alphaEqWorker rewritesFirst1 rewritesFirst2
            <*> alphaEqWorker rewritesSecond1 rewritesSecond2
      | otherwise = return False

    compareTop
        Top { topSort = topSort1 }
        Top { topSort = topSort2 }
      =
        return (topSort1 == topSort2)

    compareStringLiteral lit1 lit2 = return (lit1 == lit2)

    compareCharLiteral lit1 lit2 = return (lit1 == lit2)

    compareApplication
        Application
            { applicationSymbolOrAlias = applicationSymbolOrAlias1
            , applicationChildren = applicationChildren1
            }
        Application
            { applicationSymbolOrAlias = applicationSymbolOrAlias2
            , applicationChildren = applicationChildren2
            }
      | applicationSymbolOrAlias1 == applicationSymbolOrAlias2 =
        compareChildren applicationChildren1 applicationChildren2
      | otherwise = return False

    compareVariable var1 var2 = do
        (ctx1, ctx2) <- Reader.ask
        case (elemIndex var1 ctx1, elemIndex var2 ctx2) of
            (Just i, Just j) -> return (i == j)
            _ -> return (var1 == var2)

    compareDomainValue
        :: (level ~ Object, Ord (var level))
        => DomainValue level Domain.Builtin
            (PurePattern level Domain.Builtin var annotation)
        -> DomainValue level Domain.Builtin
            (PurePattern level Domain.Builtin var annotation)
        -> Reader ([var level], [var level]) Bool
    compareDomainValue
        DomainValue
            { domainValueSort = domainValueSort1
            , domainValueChild = domainValueChild1
            }
        DomainValue
            { domainValueSort = domainValueSort2
            , domainValueChild = domainValueChild2
            }
      | domainValueSort1 == domainValueSort2 =
        compareBuiltin domainValueChild1 domainValueChild2
      | otherwise = return False

    compareBuiltin
        :: (level ~ Object, Ord (var level))
        => Domain.Builtin (PurePattern level Domain.Builtin var annotation)
        -> Domain.Builtin (PurePattern level Domain.Builtin var annotation)
        -> Reader ([var level], [var level]) Bool
    compareBuiltin dv1 dv2 =
        case (dv1, dv2) of
            (Domain.BuiltinList l1, Domain.BuiltinList l2) ->
                compareChildren (Foldable.toList l1) (Foldable.toList l2)
            (Domain.BuiltinSet s1, Domain.BuiltinSet s2) ->
                (return . and)
                    (zipWith (==) (Set.toAscList s1) (Set.toAscList s2))
            (Domain.BuiltinMap m1, Domain.BuiltinMap m2) -> do
                let
                    (keys1, values1) = unzip (Map.toAscList m1)
                    (keys2, values2) = unzip (Map.toAscList m2)
                alphaEqChildren <- compareChildren values1 values2
                return (and $ alphaEqChildren : zipWith (==) keys1 keys2)
            (Domain.BuiltinPattern p1, Domain.BuiltinPattern p2) -> do
                let worker =
                        alphaEqWorker
                            (Pure.castVoidDomainValues p1)
                            (Pure.castVoidDomainValues p2)
                return (runReader worker ([], []))
            _ -> return False
