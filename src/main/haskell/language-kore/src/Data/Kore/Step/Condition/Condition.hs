{-|
Module      : Data.Kore.Step.Condition.Condition
Description : Data structure holding a condition.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Condition.Condition
    ( EvaluatedCondition (..)
    , UnevaluatedCondition (..)
    , makeEvaluatedAnd
    , makeEvaluatedIff
    , makeEvaluatedImplies
    , makeEvaluatedNot
    , makeEvaluatedOr
    , makeUnevaluatedAnd
    ) where

import           Data.Kore.AST.Common (And (..), Iff (..), Implies (..),
                                       Not (..), Or (..), Pattern (..),
                                       Sort (..))
import           Data.Kore.AST.PureML (CommonPurePattern, asPurePattern)

-- TODO: Maybe rename
data EvaluatedCondition level
    = ConditionTrue
    | ConditionFalse
    -- This should be changed to Satisfiable or something when adding
    -- the SMT solver. When doing that, also change the make{And,Or,...}
    -- functions to return somenthing that forces reevaluation.
    | ConditionUnevaluable !(CommonPurePattern level)
  deriving Show

newtype UnevaluatedCondition level =
    UnevaluatedCondition (CommonPurePattern level)
  deriving Show

makeEvaluatedAnd
    :: Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
makeEvaluatedAnd _ ConditionFalse _ = ConditionFalse
makeEvaluatedAnd _ _ ConditionFalse = ConditionFalse
makeEvaluatedAnd _ ConditionTrue second = second
makeEvaluatedAnd _ first ConditionTrue = first
makeEvaluatedAnd sort (ConditionUnevaluable first) (ConditionUnevaluable second) =
    ConditionUnevaluable $ asPurePattern $ AndPattern $ And sort first second

-- TODO: Do I need this?
makeUnevaluatedAnd
    :: Sort level
    -> UnevaluatedCondition level
    -> UnevaluatedCondition level
    -> UnevaluatedCondition level
makeUnevaluatedAnd sort (UnevaluatedCondition first) (UnevaluatedCondition second) =
    UnevaluatedCondition $ asPurePattern $ AndPattern $ And sort first second


makeEvaluatedOr
    :: Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
makeEvaluatedOr _ ConditionTrue _ = ConditionTrue
makeEvaluatedOr _ _ ConditionTrue = ConditionTrue
makeEvaluatedOr _ ConditionFalse second = second
makeEvaluatedOr _ first ConditionFalse = first
makeEvaluatedOr sort (ConditionUnevaluable first) (ConditionUnevaluable second) =
    ConditionUnevaluable $ asPurePattern $ OrPattern $ Or sort first second

makeEvaluatedImplies
    :: Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
-- TODO: Is it reasonable to use a different thing here?
makeEvaluatedImplies _ ConditionFalse _ = ConditionTrue
makeEvaluatedImplies _ _ ConditionTrue = ConditionTrue
makeEvaluatedImplies _ ConditionTrue second = second
makeEvaluatedImplies sort first ConditionFalse = makeEvaluatedNot sort first
makeEvaluatedImplies sort (ConditionUnevaluable first) (ConditionUnevaluable second) =
    ConditionUnevaluable $ asPurePattern $ ImpliesPattern $ Implies sort first second

makeEvaluatedIff
    :: Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
-- TODO: Is it reasonable to use a different thing here?
makeEvaluatedIff sort ConditionFalse second = makeEvaluatedNot sort second
makeEvaluatedIff _ ConditionTrue second = second
makeEvaluatedIff sort first@(ConditionUnevaluable _) ConditionFalse = makeEvaluatedNot sort first
makeEvaluatedIff _ first@(ConditionUnevaluable _) ConditionTrue = first
makeEvaluatedIff sort (ConditionUnevaluable first) (ConditionUnevaluable second) =
    ConditionUnevaluable $ asPurePattern $ IffPattern $ Iff sort first second

makeEvaluatedNot
    :: Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
makeEvaluatedNot _ ConditionFalse = ConditionTrue
makeEvaluatedNot _ ConditionTrue  = ConditionFalse
makeEvaluatedNot sort (ConditionUnevaluable condition) =
    ConditionUnevaluable $ asPurePattern $ NotPattern $ Not sort condition
