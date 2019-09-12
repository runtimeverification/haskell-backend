{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Overloading
    ( overloadedConstructorSortInjectionAndEquals
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT (..)
    )
import Control.Exception
    ( assert
    )
import qualified Control.Monad.Trans as Monad.Trans
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Unify as Unify

{- | Unify an overloaded constructor application pattern with a sort injection
pattern over an (overloaded) constructor.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

If the two constructors form an overload pair, then use the sorting information
for the two overloaded constructors to directly derive the new goals
(apply the overload axiom right-to-left on the right and retry)
otherwise, return bottom, as the constructors are incompatible

 -}
overloadedConstructorSortInjectionAndEquals
    :: (SimplifierVariable variable, MonadUnify unifier)
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
overloadedConstructorSortInjectionAndEquals
    termMerger
    first@(App_ firstHead _)
    second@(App_ secondHead _)
   = do
    tools <- Simplifier.askMetadataTools
    helper tools
  where
    helper tools
      | MetadataTools.isOverloaded tools firstHead
      , Symbol.isSortInjection secondHead
      = overloadedAndEqualsOverloading termMerger tools first second
      | MetadataTools.isOverloaded tools secondHead
      , Symbol.isSortInjection firstHead
      = overloadedAndEqualsOverloading termMerger tools second first
      | otherwise = empty
overloadedConstructorSortInjectionAndEquals _ _ _ = empty

overloadedAndEqualsOverloading
    :: (SimplifierVariable variable, MonadUnify unifier)
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -> SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
overloadedAndEqualsOverloading
    termMerger
    tools
    first@(App_ firstHead _)
    second@(App_ sortInjection [App_ secondHead secondChildren])
  | MetadataTools.isOverloading tools firstHead secondHead
  = equalInjectiveHeadsAndEquals
        termMerger
        first
        (resolveOverloading sortInjection firstHead secondHead secondChildren)
  | MetadataTools.isConstructorOrOverloaded tools secondHead
  = Monad.Trans.lift $ do
        explainBottom
            "Cannot unify overloaded constructor with different injected ctor."
            first
            second
        empty
overloadedAndEqualsOverloading _ _ _ _ = empty

resolveOverloading
    :: InternalVariable variable
    => GHC.HasCallStack
    => Symbol
    -> Symbol
    -> Symbol
    -> [TermLike variable]
    -> TermLike variable
resolveOverloading
    sortInjection
    overloadedHead
    overloadingHead
    overloadingChildren
  = mkApplySymbol overloadedHead
    $ assert (length overloadedChildrenSorts == length overloadingChildrenSorts)
    $ assert (length overloadingChildren == length overloadingChildrenSorts)
    $ zipWith mkApplySymbol
        (zipWith (Symbol.coerceSortInjection sortInjection)
            overloadingChildrenSorts
            overloadedChildrenSorts
        )
        (map pure overloadingChildren)
  where
    overloadedChildrenSorts =
        Symbol.applicationSortsOperands (symbolSorts overloadedHead)
    overloadingChildrenSorts =
        Symbol.applicationSortsOperands (symbolSorts overloadingHead)
