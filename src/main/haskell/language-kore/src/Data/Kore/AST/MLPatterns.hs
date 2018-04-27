{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE Rank2Types     #-}
{-|
Module      : Data.Kore.MLPatterns
Description : Data structures and functions for handling patterns uniformly.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.AST.MLPatterns (MLPatternClass(..),
                                 MLBinderPatternClass (..),
                                 PatternFunction(..),
                                 applyPatternFunction) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Implicit.ImplicitSorts

{-|'MLPatternClass' offers a common interface to ML patterns
  (those starting with '\', except for 'Exists' and 'Forall')
-}
class MLPatternClass pat where
    getPatternType :: pat level child -> MLPatternType
    getMLPatternOperandSorts
        :: MetaOrObject level => pat level child -> [UnifiedSort]
    getMLPatternResultSort :: pat level child -> Sort level
    getPatternSorts :: pat level child -> [Sort level]
    getPatternChildren :: pat level child -> [child]

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
        :: pat level variable child -> Sort level -> variable level -> child
        -> Pattern level variable child

instance MLPatternClass And where
    getPatternType _ = AndPatternType
    getMLPatternOperandSorts x = [asUnified (andSort x), asUnified (andSort x)]
    getMLPatternResultSort = andSort
    getPatternSorts a = [andSort a]
    getPatternChildren a = [andFirst a, andSecond a]

instance MLPatternClass Bottom where
    getPatternType _ = BottomPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = bottomSort
    getPatternSorts t = [bottomSort t]
    getPatternChildren _ = []

instance MLPatternClass Ceil where
    getPatternType _ = CeilPatternType
    getMLPatternOperandSorts x = [asUnified (ceilOperandSort x)]
    getMLPatternResultSort = ceilResultSort
    getPatternSorts c = [ceilOperandSort c, ceilResultSort c]
    getPatternChildren c = [ceilChild c]

instance MLPatternClass DomainValue where
    getPatternType _ = DomainValuePatternType
    getMLPatternOperandSorts _ = [asUnified charListMetaSort]
    getMLPatternResultSort = domainValueSort
    getPatternSorts d = [domainValueSort d]
    getPatternChildren d = [domainValueChild d]

instance MLPatternClass Equals where
    getPatternType _ = EqualsPatternType
    getMLPatternOperandSorts x =
        [asUnified (equalsOperandSort x), asUnified (equalsOperandSort x)]
    getMLPatternResultSort = equalsResultSort
    getPatternSorts e = [equalsOperandSort e, equalsResultSort e]
    getPatternChildren e = [equalsFirst e, equalsSecond e]

instance MLPatternClass Floor where
    getPatternType _ = FloorPatternType
    getMLPatternOperandSorts x = [asUnified (floorOperandSort x)]
    getMLPatternResultSort = floorResultSort
    getPatternSorts f = [floorOperandSort f, floorResultSort f]
    getPatternChildren f = [floorChild f]

instance MLPatternClass Iff where
    getPatternType _ = IffPatternType
    getMLPatternOperandSorts x = [asUnified (iffSort x), asUnified (iffSort x)]
    getMLPatternResultSort = iffSort
    getPatternSorts i = [iffSort i]
    getPatternChildren i = [iffFirst i, iffSecond i]

instance MLPatternClass Implies where
    getPatternType _ = ImpliesPatternType
    getMLPatternOperandSorts x =
        [asUnified (impliesSort x), asUnified (impliesSort x)]
    getMLPatternResultSort = impliesSort
    getPatternSorts i = [impliesSort i]
    getPatternChildren i = [impliesFirst i, impliesSecond i]

instance MLPatternClass In where
    getPatternType _ = InPatternType
    getMLPatternOperandSorts x =
        [asUnified (inOperandSort x), asUnified (inOperandSort x)]
    getMLPatternResultSort = inResultSort
    getPatternSorts i = [inOperandSort i, inResultSort i]
    getPatternChildren i = [inContainedChild i, inContainingChild i]

instance MLPatternClass Next where
    getPatternType _ = NextPatternType
    getMLPatternOperandSorts x = [asUnified (nextSort x)]
    getMLPatternResultSort = nextSort
    getPatternSorts e = [nextSort e]
    getPatternChildren e = [nextChild e]

instance MLPatternClass Not where
    getPatternType _ = NotPatternType
    getMLPatternOperandSorts x = [asUnified (notSort x)]
    getMLPatternResultSort = notSort
    getPatternSorts n = [notSort n]
    getPatternChildren n = [notChild n]

instance MLPatternClass Or where
    getPatternType _ = OrPatternType
    getMLPatternOperandSorts x = [asUnified (orSort x), asUnified (orSort x)]
    getMLPatternResultSort = orSort
    getPatternSorts a = [orSort a]
    getPatternChildren a = [orFirst a, orSecond a]

instance MLPatternClass Rewrites where
    getPatternType _ = RewritesPatternType
    getMLPatternOperandSorts x =
        [asUnified (rewritesSort x), asUnified (rewritesSort x)]
    getMLPatternResultSort = rewritesSort
    getPatternSorts e = [rewritesSort e]
    getPatternChildren e = [rewritesFirst e, rewritesSecond e]

instance MLPatternClass Top where
    getPatternType _ = TopPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = topSort
    getPatternSorts t = [topSort t]
    getPatternChildren _ = []

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

{-|`PatternFunction` holds a full set of functions that
can be applied to the elements of a `Pattern` (e.g. `Implies`). Together
with `applyPatternFunction` they form a function on patterns, hence the name.
-}
-- TODO: consider parameterizing on variable also
data PatternFunction level child result = PatternFunction
    { patternFunctionML
        :: !(forall patt . MLPatternClass patt => patt level child -> result)
    , patternFunctionMLBinder
        :: !(forall patt . MLBinderPatternClass patt
        => patt level Variable child
        -> result)
    , stringFunction :: StringLiteral -> result
    , charFunction :: CharLiteral -> result
    , applicationFunction :: !(Application level child -> result)
    , variableFunction :: !(Variable level -> result)
    }

{-|`applyPatternFunction` applies a patternFunction on the inner element of a
`Pattern`, returning the result.
-}
applyPatternFunction
    :: PatternFunction level child result
    -> Pattern level Variable child
    -> result
applyPatternFunction function (AndPattern a) =
    patternFunctionML function a
applyPatternFunction function (ApplicationPattern a) =
    applicationFunction function a
applyPatternFunction function (BottomPattern a) =
    patternFunctionML function a
applyPatternFunction function (CeilPattern a) =
    patternFunctionML function a
applyPatternFunction function (DomainValuePattern a) =
    patternFunctionML function a
applyPatternFunction function (EqualsPattern a) =
    patternFunctionML function a
applyPatternFunction function (ExistsPattern a) =
    patternFunctionMLBinder function a
applyPatternFunction function (FloorPattern a) =
    patternFunctionML function a
applyPatternFunction function (ForallPattern a) =
    patternFunctionMLBinder function a
applyPatternFunction function (IffPattern a) =
    patternFunctionML function a
applyPatternFunction function (ImpliesPattern a) =
    patternFunctionML function a
applyPatternFunction function (InPattern a) =
    patternFunctionML function a
applyPatternFunction function (NextPattern a) =
    patternFunctionML function a
applyPatternFunction function (NotPattern a) =
    patternFunctionML function a
applyPatternFunction function (OrPattern a) =
    patternFunctionML function a
applyPatternFunction function (RewritesPattern a) =
    patternFunctionML function a
applyPatternFunction function (StringLiteralPattern a) =
    stringFunction function a
applyPatternFunction function (CharLiteralPattern a) =
    charFunction function a
applyPatternFunction function (TopPattern a) =
    patternFunctionML function a
applyPatternFunction function (VariablePattern a) =
    variableFunction function a
