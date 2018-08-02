{-|
Module      : Kore.Variables.Sort
Description : Specifies the 'TermWithSortVariablesClass' which is meant to
              define a term with sort variables and exports 'sortVariables'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Sort
    ( TermWithSortVariablesClass(sortVariables)
    ) where

import           Data.Foldable
                 ( fold )
import           Data.Functor.Foldable
                 ( cata )
import           Data.List
                 ( foldl' )
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.ASTTraversals
import Kore.MetaML.AST


{-| 'TermWithSortVariableClass' links a @term@ type with a @var@ type and
provides 'sortVariables' for extracting the set of sort variables of a term.
-}
class TermWithSortVariablesClass term var where
    sortVariables :: term -> Set.Set var

instance TermWithSortVariablesClass CommonKorePattern UnifiedSortVariable
  where
    sortVariables = patternBottomUpVisitor sortVarsVisitor
      where
        sortVarsVisitor p =
            addPatternSortVariables p (addSortVariables asUnified) (fold p)

instance TermWithSortVariablesClass CommonMetaPattern (SortVariable Meta) where
    sortVariables = cata sortVarsVisitor
      where
        sortVarsVisitor p =
            addPatternSortVariables p (addSortVariables id) (fold p)

addSortVariables
    :: Ord sortVariable
    => (SortVariable level -> sortVariable)
    -> Set.Set sortVariable
    -> Sort level
    -> Set.Set sortVariable
addSortVariables
    transformer existing (SortActualSort SortActual {sortActualSorts = s})
  =
    foldl' (addSortVariables transformer) existing s
addSortVariables
    transformer existing (SortVariableSort v)
  =
    Set.insert (transformer v) existing

addPatternSortVariables
    :: Pattern level Variable child
    -> (Set.Set sortvar -> Sort level -> Set.Set sortvar)
    -> Set.Set sortvar
    -> Set.Set sortvar
addPatternSortVariables pattern1 addSortVariables1 existing =
    applyPatternFunction
        PatternFunction
            { patternFunctionML =
                \a -> addMLPatternSortVariables a addSortVariables1 existing
            , patternFunctionMLBinder =
                \a -> addBinderPatternSortVariables a addSortVariables1 existing
            , stringFunction = const existing
            , charFunction = const existing
            -- TODO: can domain value patterns have sort variables?
            , domainValueFunction = const existing
            , applicationFunction =
                \a -> addApplicationPatternSortVariables
                    a addSortVariables1 existing
            , variableFunction =
                \a -> addVariableSort a addSortVariables1 existing
            }
        pattern1

addMLPatternSortVariables
    :: (MLPatternClass p level)
    => p level child
    -> (Set.Set sortvar -> Sort level -> Set.Set sortvar)
    -> Set.Set sortvar
    -> Set.Set sortvar
addMLPatternSortVariables pattern1 addSortVariables1 existingVariables =
    foldl' addSortVariables1 existingVariables (getPatternSorts pattern1)

addBinderPatternSortVariables
    :: (MLBinderPatternClass p)
    => p level Variable child
    -> (Set.Set sortvar -> Sort level -> Set.Set sortvar)
    -> Set.Set sortvar
    -> Set.Set sortvar
addBinderPatternSortVariables pattern1 addSortVariables1 existingVariables =
    addVariableSort
        (getBinderPatternVariable pattern1)
        addSortVariables1
        (addSortVariables1
            existingVariables
            (getBinderPatternSort pattern1)
        )

addVariableSort
    :: Variable level
    -> (Set.Set sortvar -> Sort level -> Set.Set sortvar)
    -> Set.Set sortvar
    -> Set.Set sortvar
addVariableSort
    Variable {variableSort = s}
    addSortVariables1
    existingVariables
  =
    addSortVariables1 existingVariables s

addApplicationPatternSortVariables
    :: Application level child
    -> (Set.Set sortvar -> Sort level -> Set.Set sortvar)
    -> Set.Set sortvar
    -> Set.Set sortvar
addApplicationPatternSortVariables
    Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasParams = params }
        }
    addSortVariables1
    existingVars
  =
    foldl' addSortVariables1 existingVars params
