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

newtype NotSimplifier simplifier variable =
    NotSimplifier
        { runNotSimplifier
            :: SideCondition variable
            -> OrPattern variable
            -> simplifier (OrPattern variable)
        }
