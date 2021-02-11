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
    ( TermLike
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Logic
    ( LogicT
    )

-- | Unifies two 'TermLike' patterns under the given 'SideCondition'.
newtype UnificationProcedure unifier =
    UnificationProcedure
        { runUnificationProcedure
            :: SideCondition RewritingVariableName
            -> TermLike RewritingVariableName
            -> TermLike RewritingVariableName
            -> LogicT unifier (Condition RewritingVariableName)
        }
