{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Unification.UnificationProcedure
    ( UnificationProcedure (..)
    ) where

import Kore.Internal.Condition
    ( Condition
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import Logic
    ( LogicT
    )

-- | Unifies two 'TermLike' patterns under the given 'SideCondition'.
newtype UnificationProcedure unifier =
    UnificationProcedure
        { runUnificationProcedure
            :: forall variable
            .  InternalVariable variable
            => SideCondition variable
            -> TermLike variable
            -> TermLike variable
            -> LogicT unifier (Condition variable)
        }
