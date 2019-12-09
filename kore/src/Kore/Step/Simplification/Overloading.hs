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
import Data.Text.Prettyprint.Doc
    ( Doc
    )
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import qualified Kore.Attribute.Symbol as Attribute
import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.Internal.Inj as Inj
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
    (Inj_ secondInj)
   = do
    tools <- Simplifier.askMetadataTools
    if MetadataTools.isOverloaded tools firstHead
        then overloadedAndEqualsOverloading termMerger tools first secondInj
        else empty
overloadedConstructorSortInjectionAndEquals
    termMerger
    (Inj_ firstInj)
    second@(App_ secondHead _)
   = do
    tools <- Simplifier.askMetadataTools
    if MetadataTools.isOverloaded tools secondHead
        then overloadedAndEqualsOverloading termMerger tools second firstInj
        else empty
overloadedConstructorSortInjectionAndEquals _ _ _ = empty

overloadedAndEqualsOverloading
    :: (SimplifierVariable variable, MonadUnify unifier)
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -> SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> Inj (TermLike variable)
    -> MaybeT unifier (Pattern variable)
overloadedAndEqualsOverloading
    termMerger
    tools
    first@(App_ firstHead _)
    second@Inj { injChild }
  | App_ secondHead secondChildren <- injChild
  , MetadataTools.isOverloading tools firstHead secondHead
  = equalInjectiveHeadsAndEquals
        termMerger
        first
        (resolveOverloading injProto firstHead secondChildren)
  | Just typeName <- notUnifiableType injChild
  = Monad.Trans.lift $ do
        explainBottom
            ("Cannot unify overloaded constructor with " <> typeName <> ".")
            first
            (synthesize $ InjF second)
        empty
  where
    injProto = () <$ second

    notUnifiableType :: TermLike variable -> Maybe (Doc ())
    notUnifiableType (App_ appHead _)
      | MetadataTools.isConstructorOrOverloaded tools appHead
      = Just "different injected ctor"
    notUnifiableType (DV_ _ _) = Just "injected domain value"
    notUnifiableType (BuiltinBool_ _) = Just "injected builtin bool"
    notUnifiableType (BuiltinInt_ _) = Just "injected builtin int"
    notUnifiableType (BuiltinList_ _) = Just "injected builtin list"
    notUnifiableType (BuiltinMap_ _) = Just "injected builtin map"
    notUnifiableType (BuiltinSet_ _) = Just "injected builtin set"
    notUnifiableType (BuiltinString_ _) = Just "injected builtin string"
    notUnifiableType _ = Nothing
overloadedAndEqualsOverloading _ _ _ _ = empty

resolveOverloading
    :: InternalVariable variable
    => GHC.HasCallStack
    => Inj ()
    -> Symbol
    -> [TermLike variable]
    -> TermLike variable
resolveOverloading injProto overloadedHead overloadingChildren =
    mkApplySymbol overloadedHead
    $ assert (length overloadedChildrenSorts == length overloadingChildren)
    $ zipWith mkInj overloadingChildren overloadedChildrenSorts
  where
    overloadedChildrenSorts =
        Symbol.applicationSortsOperands (symbolSorts overloadedHead)
    mkInj injChild injTo =
        (synthesize . InjF) injProto { injFrom, injTo, injChild }
      where
        injFrom = termLikeSort injChild
