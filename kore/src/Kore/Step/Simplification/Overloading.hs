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

{- |
 If the two constructors form an overload pair, apply the overloading axioms
 on the terms to make the constructors equal, then retry unification on them.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

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

{- |
 Tests whether the pair of terms can be coerced to have the same constructors
 at the top, and, if so, returns the thus obtained new pair.

 See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

 If the overloading rules are not appliable, it would return @Nothing@.
 However, if it detects an unification failure, it would return a reason
 for the failure which can be used as an explanation for it.

 Note: this algorithm is used for both matching and unification; that is why
 the first and second terms in a pair are not interchangeable.
-}
unifyOverloading
    :: MonadSimplify unifier
    => SimplifierVariable variable
    => Pair (TermLike variable)
    -> unifier
        (Either (Doc ()) (Maybe (Pair (TermLike variable))))
unifyOverloading termPair = case termPair of
    Pair
        (Inj_ inj@Inj { injChild = App_ firstHead firstChildren })
        secondTerm@(App_ secondHead _)
        -> flipPairBack <$> unifyOverloadingVsOverloaded
            secondHead
            secondTerm
            (Application firstHead firstChildren)
            inj { injChild = () }
    Pair
        firstTerm@(App_ firstHead _)
        (Inj_ inj@Inj { injChild = App_ secondHead secondChildren })
        -> unifyOverloadingVsOverloaded
            firstHead
            firstTerm
            (Application secondHead secondChildren)
            inj { injChild = () }
    Pair
        (Inj_ inj@Inj { injChild = App_ firstHead firstChildren })
        (Inj_ Inj { injChild = App_ secondHead secondChildren })
        -> unifyOverloadingCommonOverload
            (Application firstHead firstChildren)
            (Application secondHead secondChildren)
            inj { injChild = () }
    (Pair (App_ firstHead _) (Inj_ Inj { injChild })) ->
        notUnifiableTest firstHead injChild
    (Pair (Inj_ Inj { injChild }) (App_ secondHead _)) ->
        notUnifiableTest secondHead injChild
    _ -> return $ Right Nothing
  where
    flipPairBack (Right (Just (Pair x y))) = Right (Just (Pair y x))
    flipPairBack p = p
    notUnifiableTest termHead child = do
        OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
        if isOverloaded termHead
        then case notUnifiableType child of
            Just typeName -> return $ Left typeName
            Nothing -> return $ Right Nothing
        else return $ Right Nothing

unifyOverloadingCommonOverload
    :: MonadSimplify unifier
    => SimplifierVariable variable
    => Application Symbol (TermLike variable)
    -> Application Symbol (TermLike variable)
    -> Inj ()
    -> unifier
        (Either (Doc ()) (Maybe (Pair (TermLike variable))))
unifyOverloadingCommonOverload
    (Application firstHead firstChildren)
    (Application secondHead secondChildren)
    injProto@Inj { injTo }
  = do
    OverloadSimplifier
        { isOverloaded, resolveOverloading, unifyOverloadWithinBound }
        <- Simplifier.askOverloadSimplifier
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

unifyOverloadingVsOverloaded
    :: MonadSimplify unifier
    => SimplifierVariable variable
    => Symbol
    -> TermLike variable
    -> Application Symbol (TermLike variable)
    -> Inj ()
    -> unifier
        (Either (Doc ()) (Maybe (Pair (TermLike variable))))
unifyOverloadingVsOverloaded
    overloadingHead
    overloadingTerm
    (Application overloadedHead overloadedChildren)
    injProto
  = do
    OverloadSimplifier { isOverloaded, isOverloading, resolveOverloading }
        <- Simplifier.askOverloadSimplifier
    isSecondHeadConstructor <- isConstructorOrOverloaded overloadedHead
    let overloadedTerm' =
            resolveOverloading injProto overloadingHead overloadedChildren
    if isOverloading overloadingHead overloadedHead
        then return . Right . Just
            $ Pair overloadingTerm overloadedTerm'
        else if isOverloaded overloadingHead && isSecondHeadConstructor
            then return $ Left "different injected ctor"
            else return $ Right Nothing

notUnifiableType :: TermLike variable -> Maybe (Doc ())
notUnifiableType (DV_ _ _) = Just "injected domain value"
notUnifiableType (BuiltinBool_ _) = Just "injected builtin bool"
notUnifiableType (BuiltinInt_ _) = Just "injected builtin int"
notUnifiableType (BuiltinList_ _) = Just "injected builtin list"
notUnifiableType (BuiltinMap_ _) = Just "injected builtin map"
notUnifiableType (BuiltinSet_ _) = Just "injected builtin set"
notUnifiableType (BuiltinString_ _) = Just "injected builtin string"
notUnifiableType _ = Nothing

