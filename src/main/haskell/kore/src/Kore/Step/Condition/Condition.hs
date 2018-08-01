{-|
Module      : Kore.Step.Condition.Condition
Description : Data structure holding a condition.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Condition
    ( ConditionProof (..)
    , ConditionSort (..)
    , EvaluatedCondition (..)
    , UnevaluatedCondition (..)
    , makeEvaluatedAnd
    , makeEvaluatedIff
    , makeEvaluatedImplies
    , makeEvaluatedNot
    , makeEvaluatedOr
    ) where

import Kore.AST.Common
       ( And (..), Iff (..), Implies (..), Not (..), Or (..), Pattern (..),
       Sort (..) )
import Kore.AST.PureML
       ( CommonPurePattern, asPurePattern )

{--| 'ConditionProof' is a placeholder for a proof showing that a condition
evaluation was correct.
--}
data ConditionProof level = ConditionProof
    deriving (Show, Eq)

{--| 'ConditionSort' represents a sort that is meant to be used when building
conditions. Usually it is assumed that the existing condition pieces already
have this sort.
--}
newtype ConditionSort level = ConditionSort (Sort level)
    deriving (Show, Eq)

{--| 'EvaluatedCondition' holds the result of evaluating a condition.
--}
data EvaluatedCondition level
    = ConditionTrue
    | ConditionFalse
    -- This should be changed to Satisfiable or something when adding
    -- the SMT solver. When doing that, also change the make{And,Or,...}
    -- functions to return somenthing that forces reevaluation.
    | ConditionUnevaluable !(CommonPurePattern level)
  deriving (Show, Eq)

{--| 'UnevaluatedCondition' holds a condition that was not yet evaluated.
--}
newtype UnevaluatedCondition level =
    UnevaluatedCondition (CommonPurePattern level)
  deriving (Show, Eq)

{--| 'makeEvaluatedAnd' combines two evaluated conditions with an 'and',
doing some simplification.
--}
makeEvaluatedAnd
    :: ConditionSort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, ConditionProof level)
makeEvaluatedAnd _ ConditionFalse _ = (ConditionFalse, ConditionProof)
makeEvaluatedAnd _ _ ConditionFalse = (ConditionFalse, ConditionProof)
makeEvaluatedAnd _ ConditionTrue second = (second, ConditionProof)
makeEvaluatedAnd _ first ConditionTrue = (first, ConditionProof)
makeEvaluatedAnd
    (ConditionSort sort)
    (ConditionUnevaluable first)
    (ConditionUnevaluable second)
  =
    ( ConditionUnevaluable $ asPurePattern $ AndPattern $ And sort first second
    , ConditionProof
    )

{--| 'makeEvaluatedOr' combines two evaluated conditions with an 'or', doing
some simplification.
--}
makeEvaluatedOr
    :: ConditionSort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, ConditionProof level)
makeEvaluatedOr _ ConditionTrue _ = (ConditionTrue, ConditionProof)
makeEvaluatedOr _ _ ConditionTrue = (ConditionTrue, ConditionProof)
makeEvaluatedOr _ ConditionFalse second = (second, ConditionProof)
makeEvaluatedOr _ first ConditionFalse = (first, ConditionProof)
makeEvaluatedOr
    (ConditionSort sort)
    (ConditionUnevaluable first)
    (ConditionUnevaluable second)
  =
    ( ConditionUnevaluable $ asPurePattern $ OrPattern $ Or sort first second
    , ConditionProof
    )

{--| 'makeEvaluatedImplies' combines two evaluated conditions into an
implication, doing some simplification.
--}
makeEvaluatedImplies
    :: ConditionSort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, ConditionProof level)
makeEvaluatedImplies _ ConditionFalse _ = (ConditionTrue, ConditionProof)
makeEvaluatedImplies _ _ ConditionTrue = (ConditionTrue, ConditionProof)
makeEvaluatedImplies _ ConditionTrue second = (second, ConditionProof)
makeEvaluatedImplies sort first ConditionFalse =
    (fst $ makeEvaluatedNot sort first, ConditionProof)
makeEvaluatedImplies
    (ConditionSort sort)
    (ConditionUnevaluable first)
    (ConditionUnevaluable second)
  =
    ( ConditionUnevaluable $ asPurePattern $ ImpliesPattern $
        Implies sort first second
    , ConditionProof
    )

{--| 'makeEvaluatedIff' combines two evaluated conditions with an 'iff', doing
some simplification.
--}
makeEvaluatedIff
    :: ConditionSort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, ConditionProof level)
makeEvaluatedIff sort ConditionFalse second =
    (fst $ makeEvaluatedNot sort second, ConditionProof)
makeEvaluatedIff _ ConditionTrue second = (second, ConditionProof)
makeEvaluatedIff sort first@(ConditionUnevaluable _) ConditionFalse =
    (fst $ makeEvaluatedNot sort first, ConditionProof)
makeEvaluatedIff _ first@(ConditionUnevaluable _) ConditionTrue =
    (first, ConditionProof)
makeEvaluatedIff
    (ConditionSort sort)
    (ConditionUnevaluable first)
    (ConditionUnevaluable second)
  =
    ( ConditionUnevaluable $ asPurePattern $ IffPattern $ Iff sort first second
    , ConditionProof
    )

{--| 'makeEvaluatedNot' negates an evaluated condition, doing some
simplification.
--}
makeEvaluatedNot
    :: ConditionSort level
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, ConditionProof level)
makeEvaluatedNot _ ConditionFalse = (ConditionTrue, ConditionProof)
makeEvaluatedNot _ ConditionTrue  = (ConditionFalse, ConditionProof)
makeEvaluatedNot (ConditionSort sort) (ConditionUnevaluable condition) =
    ( ConditionUnevaluable $ asPurePattern $ NotPattern $ Not sort condition
    , ConditionProof
    )
