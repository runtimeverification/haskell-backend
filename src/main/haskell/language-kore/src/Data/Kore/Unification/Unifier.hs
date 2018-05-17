{-|
Module      : Data.Kore.Unification.Unifier
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.Unifier
    ( module UnifierImpl
    , module Error
    ) where

import           Data.Kore.Unification.Error       as Error (UnificationError (..))
import           Data.Kore.Unification.UnifierImpl as UnifierImpl (FunctionalProof (..),
                                                                   MetadataTools (..),
                                                                   UnificationProof (..),
                                                                   UnificationSolution (..),
                                                                   unificationProcedure)
