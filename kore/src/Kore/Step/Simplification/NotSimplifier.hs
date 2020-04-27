{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.Simplification.NotSimplifier
    ( NotSimplifier (..)
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( InternalVariable
    )

newtype NotSimplifier simplifier =
    NotSimplifier
        { runNotSimplifier
            :: forall variable
            .  InternalVariable variable
            => SideCondition variable
            -> OrPattern variable
            -> simplifier (OrPattern variable)
        }
