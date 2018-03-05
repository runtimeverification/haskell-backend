{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.MetaML.Lift where

import           Data.Fix

import           Data.Kore.AST
import           Data.Kore.ASTTraversals
import           Data.Kore.ImplicitDefinitions
import           Data.Kore.MetaML.AST

class LiftableToMetaML mixed where
    liftToMeta :: mixed -> MetaMLPattern Variable

instance LiftableToMetaML (Id Object) where
    liftToMeta = Fix . StringLiteralPattern . StringLiteral . getId

instance LiftableToMetaML (SortVariable Object) where
    liftToMeta sv = Fix $ VariablePattern Variable
        { variableName = Id $ ('#' :) $ getId $ getSortVariable sv
        , variableSort = sortMetaSort
        }

liftSortConstructor :: String -> SymbolOrAlias Meta
liftSortConstructor name = groundHead ('#' : '`' : name)

liftHeadConstructor :: String -> SymbolOrAlias Meta
liftHeadConstructor = liftSortConstructor

instance LiftableToMetaML (SortActual Object) where
    liftToMeta sa = Fix $ apply
        (liftSortConstructor (getId (sortActualName sa)))
        (fmap liftToMeta (sortActualSorts sa))

instance LiftableToMetaML (Sort Object) where
    liftToMeta (SortVariableSort sv) = liftToMeta sv
    liftToMeta (SortActualSort sv)   = liftToMeta sv

instance LiftableToMetaML [Sort Object] where
    liftToMeta = foldr (applyConsSortList . liftToMeta) nilSortListMetaPattern
      where
        applyConsSortList sort sortList =
            Fix $ apply consSortListHead [sort, sortList]

instance LiftableToMetaML [MetaMLPattern Variable] where
    liftToMeta = foldr applyConsPatternList nilPatternListMetaPattern
      where
        applyConsPatternList pat patList =
            Fix $ apply consPatternListHead [pat, patList]

instance LiftableToMetaML (Variable Object) where
    liftToMeta v = Fix $ apply variableHead
        [ liftToMeta (variableName v)
        , liftToMeta (variableSort v)]

instance LiftableToMetaML UnifiedPattern where
    liftToMeta = bottomUpVisitor liftReducer
      where
        liftReducer p = applyMetaObjectFunction
            (PatternObjectMeta p)
            (liftObjectReducer . getPatternObjectMeta)
            (Fix . getPatternObjectMeta)

liftObjectReducer
    :: Pattern Object Variable (MetaMLPattern Variable)
    -> MetaMLPattern Variable
liftObjectReducer p = case p of
    AndPattern ap -> Fix $ apply andHead
        (liftToMeta (andSort ap) : getPatternChildren ap)
    ApplicationPattern ap -> let sa = applicationSymbolOrAlias ap in
        Fix $ apply
            (liftHeadConstructor (getId (symbolOrAliasConstructor sa)))
            (map liftToMeta (symbolOrAliasParams sa) ++ applicationChildren ap)
    BottomPattern bp -> Fix $ apply bottomHead [liftToMeta (bottomSort bp)]
    CeilPattern cp -> Fix $ apply ceilHead
        [ liftToMeta (ceilOperandSort cp)
        , liftToMeta (ceilResultSort cp)
        , ceilChild cp
        ]
    EqualsPattern cp -> Fix $ apply equalsHead
        [ liftToMeta (equalsOperandSort cp)
        , liftToMeta (equalsResultSort cp)
        , equalsFirst cp
        , equalsSecond cp
        ]
    ExistsPattern ep -> Fix $ apply existsHead
        [ liftToMeta (existsSort ep)
        , liftToMeta (existsVariable ep)
        , existsChild ep
        ]
    FloorPattern cp -> Fix $ apply floorHead
        [ liftToMeta (floorOperandSort cp)
        , liftToMeta (floorResultSort cp)
        , floorChild cp
        ]
    ForallPattern ep -> Fix $ apply forallHead
        [ liftToMeta (forallSort ep)
        , liftToMeta (forallVariable ep)
        , forallChild ep
        ]
    IffPattern ap -> Fix $ apply iffHead
        (liftToMeta (iffSort ap) : getPatternChildren ap)
    ImpliesPattern ap -> Fix $ apply impliesHead
        (liftToMeta (impliesSort ap) : getPatternChildren ap)
    InPattern ap -> Fix $ apply inHead
        [ liftToMeta (inOperandSort ap)
        , liftToMeta (inResultSort ap)
        , inContainedChild ap
        , inContainingChild ap
        ]
    NextPattern ap -> Fix $ apply nextHead
        [liftToMeta (nextSort ap), nextChild ap]
    NotPattern ap -> Fix $ apply notHead
        [liftToMeta (notSort ap), notChild ap]
    OrPattern ap -> Fix $ apply orHead
        (liftToMeta (orSort ap) : getPatternChildren ap)
    RewritesPattern ap -> Fix $ apply rewritesHead
        (liftToMeta (rewritesSort ap) : getPatternChildren ap)
    TopPattern bp -> Fix $ apply topHead [liftToMeta (topSort bp)]

