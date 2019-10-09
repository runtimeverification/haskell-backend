{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.NoConfusion
    ( equalInjectiveHeadsAndEquals
    , constructorAndEqualsAssumesDifferentHeads
    )where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Error as Error
import Control.Exception
    ( assert
    )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Unify as Unify
import Kore.Unparser

{- | Unify two application patterns with equal, injective heads.

This includes constructors and sort injections.

See also: 'Attribute.isInjective', 'Attribute.isSortInjection',
'Attribute.isConstructor'

 -}
equalInjectiveHeadsAndEquals
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
equalInjectiveHeadsAndEquals
    termMerger
    (App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | isFirstInjective && isSecondInjective && firstHead == secondHead =
    Monad.Trans.lift $ do
        children <- Monad.zipWithM termMerger firstChildren secondChildren
        let merged = Foldable.foldMap Pattern.withoutTerm children
            -- TODO (thomas.tuegel): This is tricky!
            -- Unifying the symbol's children may have produced new patterns
            -- which allow evaluating the symbol. It is possible this pattern
            -- is not actually fully simplified!
            term =
                (markSimplified . mkApplySymbol firstHead)
                    (Pattern.term <$> children)
        return (Pattern.withCondition term merged)
  where
    isFirstInjective = Symbol.isInjective firstHead
    isSecondInjective = Symbol.isInjective secondHead
equalInjectiveHeadsAndEquals _ _ _ = Error.nothing

{-| Unify two constructor application patterns.

Assumes that the two patterns were already tested for equality and were found
to be different; therefore their conjunction is @\\bottom@.

 -}
constructorAndEqualsAssumesDifferentHeads
    ::  ( Eq variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
constructorAndEqualsAssumesDifferentHeads
    first@(App_ firstHead _)
    second@(App_ secondHead _)
  = do
    tools <- Simplifier.askMetadataTools
    helper tools
  where
    helper tools
      | MetadataTools.isConstructorOrOverloaded tools firstHead
      , MetadataTools.isConstructorOrOverloaded tools secondHead
      = assert (firstHead /= secondHead) $ Monad.Trans.lift $ do
            explainBottom
                "Cannot unify different constructors or incompatible \
                \sort injections."
                first
                second
            empty
      | otherwise = empty
constructorAndEqualsAssumesDifferentHeads _ _ = empty
