{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Overloading
    ( overloadedConstructorSortInjectionAndEquals
    , unifyOverloading
    -- for testing purposes
    , UnifyOverloading
    , UnifyOverloadingError (..)
    ) where

import Prelude.Kore hiding
    ( concat
    )

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Monad as Monad
import Control.Monad.Trans.Except
    ( ExceptT
    , runExceptT
    , throwE
    )
import Data.String
    ( fromString
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.Debug
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.OverloadSimplifier
import Kore.Step.Simplification.Simplify as Simplifier
    ( MonadSimplify (..)
    , TermSimplifier
    , isConstructorOrOverloaded
    )
import Kore.Unification.Unify as Unify
import Pair

-- | Describes the possible errors encountered during unification.
data UnifyOverloadingError
    = NotApplicable
    -- ^ the unification problem could not be solved by the current method
    | Clash !String
    {- ^ There was a clash, unification will fail.
         Reason for the clash is included.
    -}
  deriving (GHC.Generic, Show)

instance Semigroup UnifyOverloadingError where
    NotApplicable   <> b                = b
    a               <> NotApplicable    = a
    Clash a         <> Clash b          = Clash (a <> b)

instance SOP.Generic UnifyOverloadingError

instance SOP.HasDatatypeInfo UnifyOverloadingError

instance Debug UnifyOverloadingError

instance Diff UnifyOverloadingError

instance Monoid UnifyOverloadingError where
    mempty = NotApplicable

type UnifyOverloading unifier a = ExceptT UnifyOverloadingError unifier (Pair a)

notApplicable :: Monad unifier => UnifyOverloading unifier a
notApplicable = empty

throwBottom :: Monad unifier => String -> UnifyOverloading unifier a
throwBottom = throwE . Clash

{- |
 If the two constructors form an overload pair, apply the overloading axioms
 on the terms to make the constructors equal, then retry unification on them.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

 -}
overloadedConstructorSortInjectionAndEquals
    :: (InternalVariable variable, MonadUnify unifier)
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm
  = do
    eunifier <- lift . runExceptT
        $ unifyOverloading (Pair firstTerm secondTerm)
    case eunifier of
        Right (Pair firstTerm' secondTerm') -> lift $
            termMerger firstTerm' secondTerm'
        Left (Clash message) -> lift $
            explainAndReturnBottom (fromString message) firstTerm secondTerm
        Left NotApplicable -> empty

{- |
 Tests whether the pair of terms can be coerced to have the same constructors
 at the top, and, if so, returns the thus obtained new pair.

 See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

 If the overloading rules are not applicable, it would return @Nothing@.
 However, if it detects an unification failure, it would return a reason
 for the failure which can be used as an explanation for it.

 Note: this algorithm is used for both matching and unification; that is why
 the first and second terms in a pair are not interchangeable.
-}
unifyOverloading
    :: MonadSimplify unifier
    => InternalVariable variable
    => Pair (TermLike variable)
    -> UnifyOverloading unifier (TermLike variable)
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
        (Inj_ inj'@Inj { injChild = App_ secondHead secondChildren })
      | injFrom inj /= injFrom inj' -- this case should have been handled by now
        -> unifyOverloadingCommonOverload
            (Application firstHead firstChildren)
            (Application secondHead secondChildren)
            inj { injChild = () }
    (Pair (App_ firstHead _) (Inj_ Inj { injChild })) ->
        notUnifiableTest firstHead injChild
    (Pair (Inj_ Inj { injChild }) (App_ secondHead _)) ->
        notUnifiableTest secondHead injChild
    _ -> notApplicable
  where
    flipPairBack (Pair x y) = Pair y x
    notUnifiableTest termHead child = do
        OverloadSimplifier { isOverloaded } <- Simplifier.askOverloadSimplifier
        Monad.guard (isOverloaded termHead)
        notUnifiableError child

{- Handles the case
    inj{S1,injTo}(firstHead(firstChildren))
    vs.
    inj{S2,injTo}(secondHead(secondChildren))
  If there exists  a common overload headUnion such that
    inj{S1,injTo}(firstHead(firstChildren)) =
        inj{S,injTo}(headUnion(inj1(firstChildren)))
  and
    inj{S2,injTo}(secondHead(secondChildren)) =
        inj{S,injTo}(headUnion(inj2(secondChildren)))

  Then reduces the problem to
    inj{S,injTo}(headUnion(inj1(firstChildren)))
   vs
    inj{S,injTo}(headUnion(inj2(secondChildren)))
-}
unifyOverloadingCommonOverload
    :: MonadSimplify unifier
    => InternalVariable variable
    => Application Symbol (TermLike variable)
    -> Application Symbol (TermLike variable)
    -> Inj ()
    -> UnifyOverloading unifier (TermLike variable)
unifyOverloadingCommonOverload
    (Application firstHead firstChildren)
    (Application secondHead secondChildren)
    injProto@Inj { injTo }
  = do
    OverloadSimplifier
        { isOverloaded, resolveOverloading, unifyOverloadWithinBound }
        <- Simplifier.askOverloadSimplifier
    Monad.guard (isOverloaded firstHead && isOverloaded secondHead)
    case unifyOverloadWithinBound injProto firstHead secondHead injTo of
        Nothing -> throwBottom "overloaded constructors not unifiable"
        Just (headUnion, maybeInjUnion) ->
            let first' = resolveOverloading injProto headUnion firstChildren
                second' = resolveOverloading injProto headUnion secondChildren
                mkInj' injChild inj' = (synthesize . InjF) inj' { injChild }
                mkInj injChild = maybe injChild (mkInj' injChild) maybeInjUnion
            in return $ Pair (mkInj first') (mkInj second')

{- Handles the case
    overloadingTerm@(overloadingHead(overloadingChildren))
    vs.
    inj(overloadedHead(overloadedChildren))
  If there exists an overloading axiom such that
    inj(overloadedHead(overloadedChildren)) =
        overloadingHead(inj'(overloadedChildren))

  Then it reduces the initial problem to
    overloadingTerm@(overloadingHead(overloadingChildren))
   vs
    overloadingHead(inj'(overloadedChildren))
-}
unifyOverloadingVsOverloaded
    :: MonadSimplify unifier
    => InternalVariable variable
    => Symbol
    -> TermLike variable
    -> Application Symbol (TermLike variable)
    -> Inj ()
    -> UnifyOverloading unifier (TermLike variable)
unifyOverloadingVsOverloaded
    overloadingHead
    overloadingTerm
    (Application overloadedHead overloadedChildren)
    injProto
  = do
    OverloadSimplifier { isOverloaded, isOverloading, resolveOverloading }
        <- Simplifier.askOverloadSimplifier
    Monad.guard (isOverloaded overloadingHead)
    isSecondHeadConstructor <- isConstructorOrOverloaded overloadedHead
    Monad.guard isSecondHeadConstructor
    let overloadedTerm' =
            resolveOverloading injProto overloadingHead overloadedChildren
    if isOverloading overloadingHead overloadedHead
        then return $ Pair overloadingTerm overloadedTerm'
        else throwBottom "different injected ctor"

notUnifiableError
    :: Monad unifier => TermLike variable -> UnifyOverloading unifier a
notUnifiableError (DV_ _ _) = throwBottom "injected domain value"
notUnifiableError (BuiltinBool_ _) = throwBottom "injected builtin bool"
notUnifiableError (BuiltinInt_ _) = throwBottom "injected builtin int"
notUnifiableError (BuiltinList_ _) = throwBottom "injected builtin list"
notUnifiableError (BuiltinMap_ _) = throwBottom "injected builtin map"
notUnifiableError (BuiltinSet_ _) = throwBottom "injected builtin set"
notUnifiableError (BuiltinString_ _) = throwBottom "injected builtin string"
notUnifiableError _ = notApplicable
