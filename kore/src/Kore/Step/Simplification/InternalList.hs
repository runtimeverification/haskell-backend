{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}
module Kore.Step.Simplification.InternalList
    ( simplify
    ) where

import Prelude.Kore

import Data.Functor.Compose

import Kore.Internal.InternalList
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Logic

simplify
    :: InternalVariable variable
    => InternalList (OrPattern variable)
    -> OrPattern variable
simplify =
    traverse (Logic.scatter >>> Compose)
    >>> fmap mkBuiltinList
    >>> getCompose
    >>> fmap (Pattern.syncSort >>> fmap markSimplified)
    >>> MultiOr.observeAll
