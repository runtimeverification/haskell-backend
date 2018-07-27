{-|
Module      : Kore.Unification.Unifier
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Unifier
    ( module UnifierImpl
    , module Error
    ) where

import Kore.Unification.Error as Error
       ( UnificationError (..) )
import Kore.Unification.UnifierImpl as UnifierImpl
       ( FunctionalProof (..), UnificationProof (..), UnificationSolution (..),
       UnificationSubstitution, mapSubstitutionVariables,
       normalizeSubstitutionDuplication, unificationProcedure )
