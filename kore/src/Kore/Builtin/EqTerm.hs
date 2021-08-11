{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.EqTerm (
    EqTerm (..),
    matchEqTerm,
) where

import qualified Control.Monad as Monad
import Kore.Internal.TermLike as TermLike
import Kore.Unification.Unify as Unify
import Prelude.Kore

-- | An equality-like symbol applied to @term@-type arguments.
data EqTerm term = EqTerm
    { symbol :: !Symbol
    , operand1, operand2 :: !term
    }
    deriving stock (Show)

-- | Match an equality-like symbol pattern.
matchEqTerm ::
    -- | 'Symbol' selector
    (Symbol -> Bool) ->
    TermLike variable ->
    Maybe (EqTerm (TermLike variable))
matchEqTerm selectSymbol (App_ symbol [operand1, operand2]) = do
    Monad.guard (selectSymbol symbol)
    return EqTerm{symbol, operand1, operand2}
matchEqTerm _ _ = Nothing
