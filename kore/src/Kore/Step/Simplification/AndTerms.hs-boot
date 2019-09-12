module Kore.Step.Simplification.AndTerms where

import qualified GHC.Stack as GHC

import Branch
    ( BranchT
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
    )
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )

termAnd
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> BranchT simplifier (Pattern variable)

termUnification
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
