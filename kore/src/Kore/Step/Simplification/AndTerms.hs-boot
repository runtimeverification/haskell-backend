module Kore.Step.Simplification.AndTerms where

import Kore.Internal.Pattern
       ( Pattern )
import Kore.Internal.TermLike
       ( TermLike )
import Kore.Logger
       ( LogMessage, WithLog )
import Kore.Step.Simplification.Data
       ( BranchT, MonadSimplify )
import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.Unification.Unify
       ( MonadUnify )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    :: forall variable simplifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => TermLike variable
    -> TermLike variable
    -> BranchT simplifier (Pattern variable)

termUnification
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
