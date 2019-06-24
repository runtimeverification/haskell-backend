module Kore.Step.Simplification.Ceil
    ( makeEvaluate
    , makeEvaluateTerm
    ) where

import Kore.Internal.OrPattern
       ( OrPattern )
import Kore.Internal.OrPredicate
       ( OrPredicate )
import Kore.Internal.Pattern
       ( Pattern )
import Kore.Internal.TermLike
       ( TermLike )
import Kore.Logger
       ( LogMessage, WithLog )
import Kore.Step.Simplification.Data
       ( MonadSimplify )
import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.Unparser
       ( Unparse )
import Kore.Variables.Fresh
       ( FreshVariable )

makeEvaluate
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)

makeEvaluateTerm
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => TermLike variable
    -> simplifier (OrPredicate variable)
