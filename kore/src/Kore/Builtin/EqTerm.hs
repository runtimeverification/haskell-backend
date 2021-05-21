{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Builtin.EqTerm (
    EqTerm (..),
    matchEqTerm,
    unifyEqTerm,
) where

import qualified Control.Monad as Monad
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.NotSimplifier (
    NotSimplifier (..),
 )
import Kore.Step.Simplification.Simplify (
    TermSimplifier,
 )
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

{- | Unification for an equality-like symbol.

This function is suitable only for equality simplification.
-}
unifyEqTerm ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    NotSimplifier unifier ->
    EqTerm (TermLike RewritingVariableName) ->
    Bool ->
    unifier (Pattern RewritingVariableName)
unifyEqTerm unifyChildren (NotSimplifier notSimplifier) eqTerm value =
    do
        solution <- unifyChildren operand1 operand2 & OrPattern.gather
        let solution' = MultiOr.map eraseTerm solution
        (if value then pure else notSimplifier SideCondition.top) solution'
            >>= Unify.scatter
  where
    EqTerm{operand1, operand2} = eqTerm
    eraseTerm = Pattern.fromCondition_ . Pattern.withoutTerm
