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
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import Data.Text.Prettyprint.Doc
    ( Doc
    )
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import Kore.Attribute.Synthetic
    ( synthesize
    )
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.NoConfusion
    ( equalInjectiveHeadsAndEquals
    )
import Kore.Step.Simplification.OverloadSimplifier
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
    OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
    Monad.guard (isOverloaded firstHead)
    overloadedAndEqualsOverloading termMerger first secondInj
overloadedConstructorSortInjectionAndEquals
    termMerger
    (Inj_ firstInj)
    second@(App_ secondHead _)
  = do
    OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
    Monad.guard (isOverloaded secondHead)
    overloadedAndEqualsOverloading termMerger second firstInj
overloadedConstructorSortInjectionAndEquals
    termMerger
    first@(Inj_ inj@Inj { injTo, injChild = App_ firstHead firstChildren})
    second@(Inj_ Inj { injChild = App_ secondHead secondChildren})
  = do
    OverloadSimplifier
        { isOverloaded, resolveOverloading, unifyOverloadWithinBound }
        <- Simplifier.askOverloadSimplifier
    Monad.guard (isOverloaded firstHead && isOverloaded secondHead)
    let injProto = inj { injChild = () }
    case unifyOverloadWithinBound injProto firstHead secondHead injTo of
        Nothing -> Monad.Trans.lift
            $ explainAndReturnBottom
                "overloaded constructors not unifiable"
                first
                second
        Just (headUnion, maybeInjUnion) ->
            let first' = resolveOverloading injProto headUnion firstChildren
                second' = resolveOverloading injProto headUnion secondChildren
                mkInj' injChild inj' = (synthesize . InjF) inj' { injChild }
                mkInj injChild = maybe injChild (mkInj' injChild) maybeInjUnion
            in Monad.Trans.lift $ termMerger (mkInj first') (mkInj second')
overloadedConstructorSortInjectionAndEquals _ _ _ = empty

overloadedAndEqualsOverloading
    :: (SimplifierVariable variable, MonadUnify unifier)
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -> TermLike variable
    -> Inj (TermLike variable)
    -> MaybeT unifier (Pattern variable)
overloadedAndEqualsOverloading
    termMerger
    first@(App_ firstHead _)
    second@Inj { injChild }
  | App_ secondHead secondChildren <- injChild
  = do
    OverloadSimplifier { isOverloading, resolveOverloading } <-
        Simplifier.askOverloadSimplifier
    if isOverloading firstHead secondHead
    then equalInjectiveHeadsAndEquals
            termMerger
            first
            (resolveOverloading injProto firstHead secondChildren)
    else do
        Monad.guard =<< isConstructorOrOverloaded secondHead
        returnBottom "different injected ctor"
  | Just typeName <- notUnifiableType injChild
  = returnBottom typeName
  where
    injProto = () <$ second

    returnBottom typeName =
        Monad.Trans.lift $ do
            explainBottom
                ("Cannot unify overloaded constructor with " <> typeName <> ".")
                first
                (synthesize $ InjF second)
            empty
    notUnifiableType :: TermLike variable -> Maybe (Doc ())
    notUnifiableType (DV_ _ _) = Just "injected domain value"
    notUnifiableType (BuiltinBool_ _) = Just "injected builtin bool"
    notUnifiableType (BuiltinInt_ _) = Just "injected builtin int"
    notUnifiableType (BuiltinList_ _) = Just "injected builtin list"
    notUnifiableType (BuiltinMap_ _) = Just "injected builtin map"
    notUnifiableType (BuiltinSet_ _) = Just "injected builtin set"
    notUnifiableType (BuiltinString_ _) = Just "injected builtin string"
    notUnifiableType _ = Nothing
overloadedAndEqualsOverloading _ _ _ = empty

