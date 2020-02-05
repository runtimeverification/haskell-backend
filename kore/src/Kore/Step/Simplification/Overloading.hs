{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Overloading
    ( overloadedConstructorSortInjectionAndEquals
    , unifyOverloading
    ) where

import Prelude.Kore hiding
    ( concat
    )

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Monad.Trans as Monad.Trans
import Data.Text.Prettyprint.Doc
    ( Doc
    )

import Kore.Attribute.Synthetic
    ( synthesize
    )
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.OverloadSimplifier
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Unify as Unify
import Pair

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
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm
  = do
    eunifier <- Monad.Trans.lift (unifyOverloading (Pair firstTerm secondTerm))
    case eunifier of
        Right (Just (Pair firstTerm' secondTerm')) -> Monad.Trans.lift $
            termMerger firstTerm' secondTerm'
        Left message -> Monad.Trans.lift $
            explainAndReturnBottom message firstTerm secondTerm
        Right Nothing -> empty

unifyOverloading
    :: MonadSimplify unifier
    => SimplifierVariable variable
    => Pair (TermLike variable)
    -> unifier
        (Either (Doc ()) (Maybe (Pair (TermLike variable))))
unifyOverloading
    (Pair
        firstTerm@(App_ firstHead _)
        (Inj_ inj@Inj { injChild = App_ secondHead secondChildren })
    )
  = do
    OverloadSimplifier { isOverloaded, isOverloading, resolveOverloading } <-
        Simplifier.askOverloadSimplifier
    isSecondHeadConstructor <- isConstructorOrOverloaded secondHead
    let injProto = inj { injChild = () }
        secondTerm' = resolveOverloading injProto firstHead secondChildren
    if isOverloading firstHead secondHead
        then return . Right . Just $ Pair firstTerm secondTerm'
        else if isOverloaded firstHead && isSecondHeadConstructor
            then return $ Left "different injected ctor"
            else return $ Right Nothing
unifyOverloading
    (Pair
        (Inj_ inj@Inj { injChild = App_ firstHead firstChildren })
        secondTerm@(App_ secondHead _)
    )
  = do
    OverloadSimplifier { isOverloaded, isOverloading, resolveOverloading } <-
        Simplifier.askOverloadSimplifier
    isFirstHeadConstructor <- isConstructorOrOverloaded secondHead
    let injProto = inj { injChild = () }
        firstTerm' = resolveOverloading injProto secondHead firstChildren
    if isOverloading secondHead firstHead
        then return . Right . Just $ Pair firstTerm' secondTerm
        else if isOverloaded secondHead && isFirstHeadConstructor
            then return $ Left "different injected ctor"
            else return $ Right Nothing
unifyOverloading
    (Pair
        (Inj_ inj@Inj { injTo, injChild = App_ firstHead firstChildren })
        (Inj_ Inj { injChild = App_ secondHead secondChildren })
    )
  = do
    OverloadSimplifier
        { isOverloaded, resolveOverloading, unifyOverloadWithinBound }
        <- Simplifier.askOverloadSimplifier
    let injProto = inj { injChild = () }
    if not (isOverloaded firstHead && isOverloaded secondHead)
    then return $ Right Nothing
    else case unifyOverloadWithinBound injProto firstHead secondHead injTo of
        Nothing -> return $ Left "overloaded constructors not unifiable"
        Just (headUnion, maybeInjUnion) ->
            let first' = resolveOverloading injProto headUnion firstChildren
                second' = resolveOverloading injProto headUnion secondChildren
                mkInj' injChild inj' = (synthesize . InjF) inj' { injChild }
                mkInj injChild = maybe injChild (mkInj' injChild) maybeInjUnion
            in return . Right . Just $ Pair (mkInj first') (mkInj second')
unifyOverloading (Pair firstTerm (Inj_ Inj { injChild = App_ secondHead _ }))
  = do
    OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
    if isOverloaded secondHead
    then case notUnifiableType firstTerm of
        Just typeName -> return $ Left typeName
        Nothing -> return $ Right Nothing
    else return $ Right Nothing
unifyOverloading (Pair (Inj_ Inj { injChild = App_ firstHead _ }) secondTerm)
  = do
    OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
    if isOverloaded firstHead
    then case notUnifiableType secondTerm of
        Just typeName -> return $ Left typeName
        Nothing -> return $ Right Nothing
    else return $ Right Nothing
unifyOverloading _ = return $ Right Nothing

notUnifiableType :: TermLike variable -> Maybe (Doc ())
notUnifiableType (DV_ _ _) = Just "injected domain value"
notUnifiableType (BuiltinBool_ _) = Just "injected builtin bool"
notUnifiableType (BuiltinInt_ _) = Just "injected builtin int"
notUnifiableType (BuiltinList_ _) = Just "injected builtin list"
notUnifiableType (BuiltinMap_ _) = Just "injected builtin map"
notUnifiableType (BuiltinSet_ _) = Just "injected builtin set"
notUnifiableType (BuiltinString_ _) = Just "injected builtin string"
notUnifiableType _ = Nothing

