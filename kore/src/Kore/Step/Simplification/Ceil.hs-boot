module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.Internal.OrPredicate
       ( OrPredicate )
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
