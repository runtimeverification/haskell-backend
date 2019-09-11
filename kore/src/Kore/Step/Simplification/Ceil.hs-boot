module Kore.Step.Simplification.Ceil
    ( makeEvaluate
    , makeEvaluateTerm
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.Predicate
    ( Predicate
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
    => Predicate variable
    -> Pattern variable
    -> simplifier (OrPattern variable)

makeEvaluateTerm
    ::  forall variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate variable
    -> TermLike variable
    -> simplifier (OrPredicate variable)
