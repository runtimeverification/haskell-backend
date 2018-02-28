{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.MetaML.Lift where

import           Data.Fix

import           Data.Kore.AST
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

groundHead :: String -> SymbolOrAlias a
groundHead name = SymbolOrAlias
    { symbolOrAliasConstructor = Id name
    , symbolOrAliasParams = []
    }

constant :: SymbolOrAlias a -> Pattern a v p
constant head = apply head []

apply :: SymbolOrAlias a -> [p] -> Pattern a v p
apply head patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = head
    , applicationChildren = patterns
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

nilSortListHead :: SymbolOrAlias Meta
nilSortListHead = groundHead "#nilSortList"

consSortListHead :: SymbolOrAlias Meta
consSortListHead = groundHead "#consSortList"

nilSortListMetaPattern :: MetaMLPattern v
nilSortListMetaPattern = Fix $ constant nilSortListHead

nilPatternListHead :: SymbolOrAlias Meta
nilPatternListHead = groundHead "#nilPatternList"

consPatternListHead :: SymbolOrAlias Meta
consPatternListHead = groundHead "#consPatternList"

nilPatternListMetaPattern :: MetaMLPattern v
nilPatternListMetaPattern = Fix $ constant nilPatternListHead

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

