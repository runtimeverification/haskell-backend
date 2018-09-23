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
    , module UnificationSolution
    ) where

import Kore.Unification.Error as Error
       ( ClashReason (..), UnificationError (..) )
import Kore.Unification.UnifierImpl as UnifierImpl
       ( UnificationProof (..),
       normalizeSubstitutionDuplication )
import Kore.Unification.UnificationSolution as UnificationSolution
       ( UnificationSolution (..), UnificationSubstitution,
         mapSubstitutionVariables )
