{-|
Module      : Kore.Unification.Unifier
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Unifier
    ( module UnifierImpl
    , module Error
    , module Data
    , unificationFunction
    , UnificationFunction
    ) where

import           Control.Monad.Counter
                 ( Counter )
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Data as Data
                 ( UnificationProof (..), UnificationSubstitution,
                 mapSubstitutionVariables )
import           Kore.Unification.Error as Error
                 ( ClashReason (..), UnificationError (..) )
import           Kore.Unification.UnifierImpl as UnifierImpl
                 ( UnificationSolution (..), normalizeSubstitutionDuplication,
                 unificationProcedure )

type UnificationFunction level variable =
    MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Either
        (UnificationError level)
        (Counter
            ( PredicateSubstitution level variable
            , UnificationProof level variable
            )
        )

unificationFunction
    ::  ( SortedVariable variable
        , Ord (variable level)
        , MetaOrObject level
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Either
        (UnificationError level)
        (Counter
            ( PredicateSubstitution level variable
            , UnificationProof level variable
            )
        )
unificationFunction tools first second = do  -- Either monad
    (substitution, predicate, proof) <- unificationProcedure tools first second
    return $ return
        ( PredicateSubstitution
            { predicate = predicate
            , substitution = substitution
            }
        , proof
        )

