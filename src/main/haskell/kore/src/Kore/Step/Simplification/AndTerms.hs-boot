module Kore.Step.Simplification.AndTerms where

import Control.Error
       ( ExceptT )

import Control.Monad.Counter
       ( MonadCounter )
import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.ExpandedPattern
       ( ExpandedPattern )
import Kore.Step.Pattern
       ( StepPattern )
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Unification.Error
       ( UnificationOrSubstitutionError )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)

termUnification
    :: forall level variable m err .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> err m
        (ExpandedPattern level variable, SimplificationProof level)
