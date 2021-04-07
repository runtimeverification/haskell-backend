{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.NoConfusion
    ( equalInjectiveHeadsAndEquals
    , constructorAndEqualsAssumesDifferentHeads
    ) where

import Prelude.Kore hiding
    ( concat
    )

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Error as Error
import qualified Control.Monad as Monad

import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Unify as Unify

{- | Unify two application patterns with equal, injective heads.

This includes constructors and sort injections.

See also: 'Attribute.isInjective', 'Attribute.isSortInjection',
'Attribute.isConstructor'

 -}
equalInjectiveHeadsAndEquals
    :: MonadUnify unifier
    => HasCallStack
    => TermSimplifier RewritingVariableName unifier
    -- ^ Used to simplify subterm "and".
    -> Symbol
    -> [TermLike RewritingVariableName]
    -> Symbol
    -> [TermLike RewritingVariableName]
    -> MaybeT unifier (Pattern RewritingVariableName)
equalInjectiveHeadsAndEquals
    termMerger
    firstHead
    firstChildren
    secondHead
    secondChildren
  | isFirstInjective && isSecondInjective && firstHead == secondHead =
    lift $ do
        children <- Monad.zipWithM termMerger firstChildren secondChildren
        let merged = foldMap Pattern.withoutTerm children
            -- TODO (thomas.tuegel): This is tricky!
            -- Unifying the symbol's children may have produced new patterns
            -- which allow evaluating the symbol. It is possible this pattern
            -- is not actually fully simplified!
            term =
                (markSimplified . mkApplySymbol firstHead)
                    (Pattern.term <$> children)
        return (Pattern.withCondition term merged)
  | otherwise = Error.nothing
  where
    isFirstInjective = Symbol.isInjective firstHead
    isSecondInjective = Symbol.isInjective secondHead

{-| Unify two constructor application patterns.

Assumes that the two patterns were already tested for equality and were found
to be different; therefore their conjunction is @\\bottom@.

 -}
constructorAndEqualsAssumesDifferentHeads
    :: MonadUnify unifier
    => HasCallStack
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Symbol
    -> Symbol
    -> MaybeT unifier a
constructorAndEqualsAssumesDifferentHeads
    first
    second
    firstHead
    secondHead
  = do
    Monad.guard =<< Simplifier.isConstructorOrOverloaded firstHead
    Monad.guard =<< Simplifier.isConstructorOrOverloaded secondHead
    assert (firstHead /= secondHead) $ lift $ do
        explainBottom
            "Cannot unify different constructors or incompatible \
            \sort injections."
            first
            second
        empty
