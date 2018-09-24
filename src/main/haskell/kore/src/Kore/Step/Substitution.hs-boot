{-|
Module      : Kore.Step.Substitution.hs-boot
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
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
import Kore.Unification.UnificationSolution
       ( UnificationSubstitution )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )
import Kore.Unification.UnificationSolution
       ( UnificationProof )

mergePredicatesAndSubstitutions
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
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
