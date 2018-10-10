module Kore.Step.Substitution where

import Kore.AST.MetaOrObject
import Kore.Variables.Fresh
       ( FreshVariable )
import Kore.AST.Common
       ( SortedVariable )
import Control.Monad.Counter
       ( MonadCounter )
import Kore.Substitution.Class
       ( Hashable )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Predicate.Predicate
       ( Predicate )
import Kore.Unification.Data
       ( UnificationSubstitution, UnificationProof )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )

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
