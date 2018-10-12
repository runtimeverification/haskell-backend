module Kore.Step.Substitution where

import Control.Monad.Counter
       ( MonadCounter )
import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Predicate.Predicate
       ( Predicate )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Substitution.Class
       ( Hashable )
import Kore.Unification.Data
       ( UnificationProof, UnificationSubstitution )
import Kore.Variables.Fresh
       ( FreshVariable )

mergePredicatesAndSubstitutions
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , OrdMetaOrObject variable
       , ShowMetaOrObject variable
       , FreshVariable variable
       , MonadCounter m
       , Hashable variable
       )
    => MetadataTools level StepperAttributes
    -> [Predicate level variable]
    -> [UnificationSubstitution level variable]
    -> m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
