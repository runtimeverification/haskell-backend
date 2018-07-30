{-|
Module      : Kore.MLPatterns
Description : Data structures and functions for handling patterns uniformly.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.AST.MLPatterns
    ( MLPatternClass(..)
    , MLBinderPatternClass (..)
    , PatternFunction (..)
    , PatternLeveledFunction (..)
    , applyPatternFunction
    , applyPatternLeveledFunction
    , getPatternResultSort
    , undefinedHeadSort
    ) where

import Data.Functor.Foldable
       (Fix)

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       (ApplicationSorts (..))
import Kore.Implicit.ImplicitSorts

{-|'MLPatternClass' offers a common interface to ML patterns
  (those starting with '\', except for 'Exists' and 'Forall')
-}
class MLPatternClass pat level where
    getPatternType :: pat level child -> MLPatternType
    getMLPatternOperandSorts
        :: MetaOrObject level => pat level child -> [UnifiedSort]
    getMLPatternResultSort :: pat level child -> Sort level
    getPatternSorts :: pat level child -> [Sort level]
    getPatternChildren :: pat level child -> [child]
    mlPatternToPattern :: pat level child -> Pattern level variable child

{-|'MLBinderPatternClass' offers a common interface to the 'Exists' and 'Forall'
ML patterns.
-}
class MLBinderPatternClass pat where
    getBinderPatternType :: pat level variable child -> MLPatternType
    getBinderPatternSort :: pat level variable child -> Sort level
    getBinderPatternVariable :: pat level variable child -> variable level
    getBinderPatternChild :: pat level variable child -> child
    -- The first argument is only needed in order to make the Haskell type
    -- system work.
    binderPatternConstructor
        :: MetaOrObject level
        => pat level variable child -> Sort level -> variable level -> child
        -> Pattern level variable child
    mlBinderPatternToPattern :: pat level variable child -> Pattern level variable child

instance MLPatternClass And level where
    getPatternType _ = AndPatternType
    getMLPatternOperandSorts x = [asUnified (andSort x), asUnified (andSort x)]
    getMLPatternResultSort = andSort
    getPatternSorts a = [andSort a]
    getPatternChildren a = [andFirst a, andSecond a]
    mlPatternToPattern = AndPattern

instance MLPatternClass Bottom level where
    getPatternType _ = BottomPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = bottomSort
    getPatternSorts t = [bottomSort t]
    getPatternChildren _ = []
    mlPatternToPattern = BottomPattern

instance MLPatternClass Ceil level where
    getPatternType _ = CeilPatternType
    getMLPatternOperandSorts x = [asUnified (ceilOperandSort x)]
    getMLPatternResultSort = ceilResultSort
    getPatternSorts c = [ceilOperandSort c, ceilResultSort c]
    getPatternChildren c = [ceilChild c]
    mlPatternToPattern = CeilPattern

instance MLPatternClass Equals level where
    getPatternType _ = EqualsPatternType
    getMLPatternOperandSorts x =
        [asUnified (equalsOperandSort x), asUnified (equalsOperandSort x)]
    getMLPatternResultSort = equalsResultSort
    getPatternSorts e = [equalsOperandSort e, equalsResultSort e]
    getPatternChildren e = [equalsFirst e, equalsSecond e]
    mlPatternToPattern = EqualsPattern

instance MLPatternClass Floor level where
    getPatternType _ = FloorPatternType
    getMLPatternOperandSorts x = [asUnified (floorOperandSort x)]
    getMLPatternResultSort = floorResultSort
    getPatternSorts f = [floorOperandSort f, floorResultSort f]
    getPatternChildren f = [floorChild f]
    mlPatternToPattern = FloorPattern

instance MLPatternClass Iff level where
    getPatternType _ = IffPatternType
    getMLPatternOperandSorts x = [asUnified (iffSort x), asUnified (iffSort x)]
    getMLPatternResultSort = iffSort
    getPatternSorts i = [iffSort i]
    getPatternChildren i = [iffFirst i, iffSecond i]
    mlPatternToPattern = IffPattern

instance MLPatternClass Implies level where
    getPatternType _ = ImpliesPatternType
    getMLPatternOperandSorts x =
        [asUnified (impliesSort x), asUnified (impliesSort x)]
    getMLPatternResultSort = impliesSort
    getPatternSorts i = [impliesSort i]
    getPatternChildren i = [impliesFirst i, impliesSecond i]
    mlPatternToPattern = ImpliesPattern

instance MLPatternClass In level where
    getPatternType _ = InPatternType
    getMLPatternOperandSorts x =
        [asUnified (inOperandSort x), asUnified (inOperandSort x)]
    getMLPatternResultSort = inResultSort
    getPatternSorts i = [inOperandSort i, inResultSort i]
    getPatternChildren i = [inContainedChild i, inContainingChild i]
    mlPatternToPattern = InPattern

instance MLPatternClass Next Object where
    getPatternType _ = NextPatternType
    getMLPatternOperandSorts x = [asUnified (nextSort x)]
    getMLPatternResultSort = nextSort
    getPatternSorts e = [nextSort e]
    getPatternChildren e = [nextChild e]
    mlPatternToPattern = NextPattern

instance MLPatternClass Not level where
    getPatternType _ = NotPatternType
    getMLPatternOperandSorts x = [asUnified (notSort x)]
    getMLPatternResultSort = notSort
    getPatternSorts n = [notSort n]
    getPatternChildren n = [notChild n]
    mlPatternToPattern = NotPattern

instance MLPatternClass Or level where
    getPatternType _ = OrPatternType
    getMLPatternOperandSorts x = [asUnified (orSort x), asUnified (orSort x)]
    getMLPatternResultSort = orSort
    getPatternSorts a = [orSort a]
    getPatternChildren a = [orFirst a, orSecond a]
    mlPatternToPattern = OrPattern

instance MLPatternClass Rewrites Object where
    getPatternType _ = RewritesPatternType
    getMLPatternOperandSorts x =
        [asUnified (rewritesSort x), asUnified (rewritesSort x)]
    getMLPatternResultSort = rewritesSort
    getPatternSorts e = [rewritesSort e]
    getPatternChildren e = [rewritesFirst e, rewritesSecond e]
    mlPatternToPattern = RewritesPattern

instance MLPatternClass Top level where
    getPatternType _ = TopPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = topSort
    getPatternSorts t = [topSort t]
    getPatternChildren _ = []
    mlPatternToPattern = TopPattern

instance MLBinderPatternClass Exists where
    getBinderPatternType _ = ExistsPatternType
    getBinderPatternSort = existsSort
    getBinderPatternVariable = existsVariable
    getBinderPatternChild = existsChild
    binderPatternConstructor _ sort variable pat = ExistsPattern Exists
        { existsSort = sort
        , existsVariable = variable
        , existsChild = pat
        }
    mlBinderPatternToPattern = ExistsPattern

instance MLBinderPatternClass Forall where
    getBinderPatternType _ = ForallPatternType
    getBinderPatternSort = forallSort
    getBinderPatternVariable = forallVariable
    getBinderPatternChild = forallChild
    binderPatternConstructor _ sort variable pat = ForallPattern Forall
        { forallSort = sort
        , forallVariable = variable
        , forallChild = pat
        }
    mlBinderPatternToPattern = ForallPattern

{-|`PatternLeveledFunction` holds a full set of functions that
can be applied to the elements of a `Pattern` (e.g. `Implies`). Together
with `applyPatternLeveledFunction` they form a function on patterns, hence the name.
-}
-- TODO: consider parameterizing on variable also
data PatternLeveledFunction level variable child result = PatternLeveledFunction
    { patternLeveledFunctionML
        :: !(forall patt . MLPatternClass patt level
            => patt level child -> result level)
    , patternLeveledFunctionMLBinder
        :: !(forall patt . MLBinderPatternClass patt
        => patt level variable child
        -> result level)
    , stringLeveledFunction :: StringLiteral -> result Meta
    , charLeveledFunction :: CharLiteral -> result Meta
    , domainValueLeveledFunction
        :: DomainValue Object (Fix (Pattern Meta Variable)) -> result Object
    , applicationLeveledFunction :: !(Application level child -> result level)
    , variableLeveledFunction :: !(variable level -> result level)
    }

{-|`applyPatternLeveledFunction` applies a patternFunction on the inner element of a
`Pattern`, returning the result.
-}
applyPatternLeveledFunction
    :: PatternLeveledFunction level variable child result
    -> Pattern level variable child
    -> result level
applyPatternLeveledFunction function (AndPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (ApplicationPattern a) =
    applicationLeveledFunction function a
applyPatternLeveledFunction function (BottomPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (CeilPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (DomainValuePattern a) =
    domainValueLeveledFunction function a
applyPatternLeveledFunction function (EqualsPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (ExistsPattern a) =
    patternLeveledFunctionMLBinder function a
applyPatternLeveledFunction function (FloorPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (ForallPattern a) =
    patternLeveledFunctionMLBinder function a
applyPatternLeveledFunction function (IffPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (ImpliesPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (InPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (NextPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (NotPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (OrPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (RewritesPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (StringLiteralPattern a) =
    stringLeveledFunction function a
applyPatternLeveledFunction function (CharLiteralPattern a) =
    charLeveledFunction function a
applyPatternLeveledFunction function (TopPattern a) =
    patternLeveledFunctionML function a
applyPatternLeveledFunction function (VariablePattern a) =
    variableLeveledFunction function a

{-|`PatternFunction` holds a full set of functions that
can be applied to the elements of a `Pattern` (e.g. `Implies`). Together
with `applyPatternFunction` they form a function on patterns, hence the name.
-}
-- TODO: consider parameterizing on variable also
data PatternFunction level variable child result = PatternFunction
    { patternFunctionML
        :: !(forall patt . MLPatternClass patt level => patt level child -> result)
    , patternFunctionMLBinder
        :: !(forall patt . MLBinderPatternClass patt
        => patt level variable child
        -> result)
    , stringFunction :: StringLiteral -> result
    , charFunction :: CharLiteral -> result
    , applicationFunction :: !(Application level child -> result)
    , variableFunction :: !(variable level -> result)
    , domainValueFunction
        :: DomainValue Object (Fix (Pattern Meta Variable)) -> result
    }

newtype ParameterizedProxy result level = ParameterizedProxy
    { getParameterizedProxy :: result }

{-|`applyPatternFunction` applies a patternFunction on the inner element of a
`Pattern`, returning the result.
-}
applyPatternFunction
    :: PatternFunction level variable child result
    -> Pattern level variable child
    -> result
applyPatternFunction patternFunction =
    getParameterizedProxy
    . applyPatternLeveledFunction
        PatternLeveledFunction
            { patternLeveledFunctionML =
                ParameterizedProxy . patternFunctionML patternFunction
            , patternLeveledFunctionMLBinder =
                ParameterizedProxy . patternFunctionMLBinder patternFunction
            , stringLeveledFunction =
                ParameterizedProxy . stringFunction patternFunction
            , charLeveledFunction =
                ParameterizedProxy . charFunction patternFunction
            , applicationLeveledFunction =
                ParameterizedProxy . applicationFunction patternFunction
            , variableLeveledFunction =
                ParameterizedProxy . variableFunction patternFunction
            , domainValueLeveledFunction =
                ParameterizedProxy . domainValueFunction patternFunction
            }

-- |'getPatternResultSort' retrieves the result sort of a pattern.
--
-- Since the sort of 'Application' patterns is not contained within
-- the term itself, it takes as firts argument a function yielding the
-- result sort corresponding to an application head.
-- TODO(traiansf): add tests.
getPatternResultSort
    :: SortedVariable variable
    => (SymbolOrAlias level -> ApplicationSorts level)
    -- ^Function to retrieve the sort of a given pattern Head
    -> Pattern level variable child
    -> Sort level
getPatternResultSort applicationSorts =
    applyPatternLeveledFunction PatternLeveledFunction
        { patternLeveledFunctionML = getMLPatternResultSort
        , patternLeveledFunctionMLBinder = getBinderPatternSort
        , stringLeveledFunction = const stringMetaSort
        , charLeveledFunction = const charMetaSort
        , domainValueLeveledFunction = domainValueSort
        , applicationLeveledFunction =
            applicationSortsResult . applicationSorts . applicationSymbolOrAlias
        , variableLeveledFunction = sortedVariableSort
        }

-- |Sample argument function for 'getPatternResultSort', failing for all input.
undefinedHeadSort :: SymbolOrAlias level -> ApplicationSorts level
undefinedHeadSort _ =
    error "Application pattern sort currently undefined"
