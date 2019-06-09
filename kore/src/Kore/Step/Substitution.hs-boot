module Kore.Step.Substitution where

import GHC.Stack
       ( HasCallStack )

import           Kore.Internal.Pattern
                 ( Predicate )
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Substitution
                 ( Substitution )
import           Kore.Unification.Unify
                 ( MonadUnify )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

mergePredicatesAndSubstitutionsExcept
    ::  ( Show variable
        , SortedVariable variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        , HasCallStack
        , MonadUnify unifier
        , WithLog LogMessage unifier
        )
    => [Syntax.Predicate variable]
    -> [Substitution variable]
    -> unifier (Predicate variable)
