module Kore.Step.Simplification.Ceil
    ( makeEvaluate
    , makeEvaluateTerm
    ) where

import Kore.Internal.Condition
    ( Condition
    )
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )

makeEvaluate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Condition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)

makeEvaluateTerm
    ::  forall variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Condition variable
    -> TermLike variable
    -> simplifier (OrCondition variable)
