module Kore.Step.Simplification.AndTerms where

import Control.Monad.Counter
       ( MonadCounter )
import Kore.AST.Common
       ( PureMLPattern, SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.ExpandedPattern
       ( ExpandedPattern )
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Substitution.Class
       ( Hashable )
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)

termUnification
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (m (ExpandedPattern level variable, SimplificationProof level))
