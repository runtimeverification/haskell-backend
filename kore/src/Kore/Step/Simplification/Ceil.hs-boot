module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.Internal.OrPredicate
       ( OrPredicate )
import Kore.Internal.TermLike
       ( TermLike )
import Kore.Step.Simplification.Data
       ( Simplifier )
import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.Unparser
       ( Unparse )
import Kore.Variables.Fresh
       ( FreshVariable )

makeEvaluateTerm
    ::  forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> Simplifier (OrPredicate variable)
