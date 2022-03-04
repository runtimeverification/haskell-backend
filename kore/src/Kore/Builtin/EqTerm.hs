{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.EqTerm (
    EqTerm (..),
    matchEqTerm,
    unifyEqTerm,
) where

import Control.Monad qualified as Monad
import Kore.Internal.ApplicationSorts (applicationSortsResult)
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.NotSimplifier (
    NotSimplifier (..),
 )
import Kore.Simplify.Simplify (
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
        (if value then pure else mkNotSimplified) solution'
            >>= Unify.scatter
  where
    EqTerm{symbol, operand1, operand2} = eqTerm
    eqSort = applicationSortsResult . symbolSorts $ symbol
    eraseTerm conditional = conditional $> (mkTop eqSort)
    mkNotSimplified notChild =
        notSimplifier SideCondition.top Not{notSort = eqSort, notChild}
