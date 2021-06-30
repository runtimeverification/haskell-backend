{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Simplify.Overloading (
    matchOverloading,
    -- for testing purposes
    unifyOverloading,
    UnifyOverloadingResult,
    MatchOverloadingResult,
    UnifyOverloadingError (..),
    Narrowing (..),
    OverloadingResolution (..),
) where

import qualified Control.Monad as Monad
import Control.Monad.Trans.Except (
    ExceptT,
    catchE,
    throwE,
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Debug
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.OverloadSimplifier
import Kore.Simplify.Simplify as Simplifier (
    MonadSimplify (..),
    isConstructorOrOverloaded,
 )
import Pair
import Prelude.Kore hiding (
    concat,
 )

-- | Overload solution requiring narrowing
data Narrowing variable = Narrowing
    { -- |narrowing substitution represented as a 'Condition'
      narrowingSubst :: !(Condition variable)
    , -- |the fresh variables within the narrowingSubst
      narrowingVars :: ![ElementVariable variable]
    , overloadPair :: !(Pair (TermLike variable))
    -- overload solution
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

-- | Result of applying the 'unifyOverloading' resolution procedure
data OverloadingResolution variable
    = -- |The overloading resolves yielding the transformed pair of terms
      Simple !(Pair (TermLike variable))
    | -- |Overloading resolves, but additional narrowing is needed for solution
      WithNarrowing !(Narrowing variable)
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

-- | Describes the possible errors encountered during unification.
data UnifyOverloadingError
    = -- | the unification problem could not be solved by the current method
      NotApplicable
    | -- | There was a clash, unification will fail.
      --         Reason for the clash is included.
      Clash !String
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Semigroup UnifyOverloadingError where
    NotApplicable <> b = b
    a <> NotApplicable = a
    Clash a <> Clash b = Clash (a <> b)

instance Monoid UnifyOverloadingError where
    mempty = NotApplicable

type UnifyOverloadingResult unifier variable =
    ExceptT UnifyOverloadingError unifier (OverloadingResolution variable)

type MatchOverloadingResult unifier variable =
    ExceptT
        UnifyOverloadingError
        unifier
        (Pair (TermLike variable))

type OverloadingResult unifier a = ExceptT UnifyOverloadingError unifier a

notApplicable :: Monad unifier => OverloadingResult unifier a
notApplicable = empty

throwBottom :: Monad unifier => String -> OverloadingResult unifier a
throwBottom = throwE . Clash

matchOverloading ::
    MonadSimplify unifier =>
    Pair (TermLike RewritingVariableName) ->
    MatchOverloadingResult unifier RewritingVariableName
matchOverloading termPair =
    do
        unifyResult <- unifyOverloading termPair
        case unifyResult of
            Simple pair -> return pair
            _ -> notApplicable

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
unifyOverloading ::
    forall unifier.
    MonadSimplify unifier =>
    Pair (TermLike RewritingVariableName) ->
    UnifyOverloadingResult unifier RewritingVariableName
unifyOverloading termPair = case termPair of
    Pair
        (Inj_ inj@Inj{injChild = App_ firstHead firstChildren})
        secondTerm@(App_ secondHead _) ->
            Simple . flipPairBack
                <$> unifyOverloadingVsOverloaded
                    secondHead
                    secondTerm
                    (Application firstHead firstChildren)
                    inj{injChild = ()}
    Pair
        firstTerm@(App_ firstHead _)
        (Inj_ inj@Inj{injChild = App_ secondHead secondChildren}) ->
            Simple
                <$> unifyOverloadingVsOverloaded
                    firstHead
                    firstTerm
                    (Application secondHead secondChildren)
                    inj{injChild = ()}
    Pair
        (Inj_ inj@Inj{injChild = App_ firstHead firstChildren})
        (Inj_ inj'@Inj{injChild = App_ secondHead secondChildren})
            | injFrom inj /= injFrom inj' -> -- this case should have been handled by now
                Simple
                    <$> unifyOverloadingCommonOverload
                        (Application firstHead firstChildren)
                        (Application secondHead secondChildren)
                        inj{injChild = ()}
    Pair firstTerm secondTerm ->
        catchE
            (worker firstTerm secondTerm)
            ( \case
                NotApplicable -> worker secondTerm firstTerm
                clash -> throwE clash
            )
  where
    worker ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        UnifyOverloadingResult unifier RewritingVariableName
    worker
        firstTerm@(App_ firstHead _)
        (Inj_ inj@Inj{injChild = ElemVar_ secondVar}) =
            unifyOverloadingVsOverloadedVariable
                firstHead
                firstTerm
                secondVar
                inj{injChild = ()}
    worker
        (Inj_ Inj{injChild = firstTerm@(App_ firstHead firstChildren)})
        (Inj_ inj@Inj{injChild = ElemVar_ secondVar}) =
            unifyOverloadingInjVsVariable
                (Application firstHead firstChildren)
                secondVar
                (Attribute.freeVariables firstTerm)
                inj{injChild = ()}
    worker (App_ firstHead _) (Inj_ Inj{injChild}) =
        notUnifiableTest firstHead injChild
    worker _ _ = notApplicable

    flipPairBack (Pair x y) = Pair y x
    notUnifiableTest termHead child = do
        OverloadSimplifier{isOverloaded} <- Simplifier.askOverloadSimplifier
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
unifyOverloadingCommonOverload ::
    MonadSimplify unifier =>
    Application Symbol (TermLike RewritingVariableName) ->
    Application Symbol (TermLike RewritingVariableName) ->
    Inj () ->
    MatchOverloadingResult unifier RewritingVariableName
unifyOverloadingCommonOverload
    (Application firstHead firstChildren)
    (Application secondHead secondChildren)
    injProto@Inj{injTo} =
        do
            OverloadSimplifier
                { isOverloaded
                , resolveOverloading
                , unifyOverloadWithinBound
                } <-
                Simplifier.askOverloadSimplifier
            Monad.guard (isOverloaded firstHead && isOverloaded secondHead)
            case unifyOverloadWithinBound injProto firstHead secondHead injTo of
                Nothing -> notUnifiableOverloads
                Just InjectedOverload{overload, injectionHead} ->
                    let first' = resolveOverloading injProto overload firstChildren
                        second' = resolveOverloading injProto overload secondChildren
                        mkInj' = maybeMkInj injectionHead
                     in return $ Pair (mkInj' first') (mkInj' second')

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
unifyOverloadingVsOverloaded ::
    MonadSimplify unifier =>
    Symbol ->
    TermLike RewritingVariableName ->
    Application Symbol (TermLike RewritingVariableName) ->
    Inj () ->
    MatchOverloadingResult unifier RewritingVariableName
unifyOverloadingVsOverloaded
    overloadingHead
    overloadingTerm
    (Application overloadedHead overloadedChildren)
    injProto =
        do
            OverloadSimplifier{isOverloaded, isOverloading, resolveOverloading} <-
                Simplifier.askOverloadSimplifier
            Monad.guard (isOverloaded overloadingHead)
            isSecondHeadConstructor <- isConstructorOrOverloaded overloadedHead
            Monad.guard isSecondHeadConstructor
            let ~overloadedTerm' =
                    resolveOverloading injProto overloadingHead overloadedChildren
            if isOverloading overloadingHead overloadedHead
                then return $ Pair overloadingTerm overloadedTerm'
                else throwBottom "different injected ctor"

{- Handles the case
    overloadingTerm@(overloadingHead(overloadingChildren))
    vs.
    inj{S2,injTo}(overloadedVariable)
  If there exists a (unique) maximum overloadedHead with its result sort S2'
  within S2 such that
    inj{S2',injTo}(overloadedHead(freshVars)) =
        overloadingHead(inj2(freshVars))

  Then it narrows overloadedVariable to inj{S2',S2}(overloadedHead(freshVars))
  and reduces the initial problem to
    overloadingTerm@(overloadingHead(overloadingChildren))
   vs
    overloadingHead(inj2(freshVars))
-}
unifyOverloadingVsOverloadedVariable ::
    MonadSimplify unifier =>
    Symbol ->
    TermLike RewritingVariableName ->
    ElementVariable RewritingVariableName ->
    Inj () ->
    UnifyOverloadingResult unifier RewritingVariableName
unifyOverloadingVsOverloadedVariable
    overloadingHead
    overloadingTerm
    overloadedVar
    injProto@Inj{injFrom} =
        do
            OverloadSimplifier{isOverloaded, getOverloadedWithinSort} <-
                Simplifier.askOverloadSimplifier
            Monad.guard (isOverloaded overloadingHead)
            case getOverloadedWithinSort injProto overloadingHead injFrom of
                Right Nothing -> notUnifiableOverloads
                Right (Just overHead) ->
                    WithNarrowing
                        <$> computeNarrowing
                            overloadingTerm
                            Nothing
                            overloadingHead
                            injProto
                            freeVars
                            overloadedVar
                            overHead
                Left err -> error err
      where
        freeVars = freeVariables overloadingTerm

{- Handles the case
    inj{S1,injTo}(firstHead(firstChildren))
    vs.
    inj{S2,injTo}(secondVariable)
  If there exists a (unique) maximum overloadedHead' with its result sort
  S2' within S2, such that there exists a common overload headUnion such that
    inj{S1,injTo}(firstHead(firstChildren)) =
        inj{S,injTo}(headUnion(inj1(firstChildren)))
  and
    inj{S2',injTo}(secondHead(freshVars)) =
        inj{S,injTo}(headUnion(inj2(freshVars)))

  Then it narrows overloadedVariable to inj{S2',S2}(secondHead(freshVars))
  and reduces the problem to
    inj{S,injTo}(headUnion(inj1(firstChildren)))
   vs
    inj{S,injTo}(headUnion(inj2(freshVars)))
-}
unifyOverloadingInjVsVariable ::
    MonadSimplify unifier =>
    Application Symbol (TermLike RewritingVariableName) ->
    ElementVariable RewritingVariableName ->
    Attribute.FreeVariables RewritingVariableName ->
    Inj () ->
    UnifyOverloadingResult unifier RewritingVariableName
unifyOverloadingInjVsVariable
    (Application firstHead firstChildren)
    overloadedVar
    freeVars
    injProto =
        do
            OverloadSimplifier
                { isOverloaded
                , resolveOverloading
                , unifyOverloadWithSortWithinBound
                } <-
                Simplifier.askOverloadSimplifier
            Monad.guard (isOverloaded firstHead)
            case unifyOverloadWithSortWithinBound firstHead injProto of
                Left err -> error err
                Right Nothing -> notUnifiableOverloads
                Right
                    (Just InjectedOverloadPair{overloadingSymbol, overloadedSymbol}) ->
                        do
                            let (InjectedOverload headUnion maybeInjUnion) = overloadingSymbol
                                first' = resolveOverloading injProto headUnion firstChildren
                            WithNarrowing
                                <$> computeNarrowing
                                    first'
                                    maybeInjUnion
                                    headUnion
                                    injProto
                                    freeVars
                                    overloadedVar
                                    overloadedSymbol

computeNarrowing ::
    HasCallStack =>
    MonadSimplify unifier =>
    -- |overloading pair LHS
    TermLike RewritingVariableName ->
    -- |optional injection
    Maybe (Inj ()) ->
    -- |overloading symbol
    Symbol ->
    -- |injection to overloading symbol
    Inj () ->
    -- |free vars in the unification pair
    Attribute.FreeVariables RewritingVariableName ->
    -- |injected variable (to be narrowed)
    ElementVariable RewritingVariableName ->
    -- |overloaded symbol injected into the variable's sort
    InjectedOverload ->
    ExceptT UnifyOverloadingError unifier (Narrowing RewritingVariableName)
computeNarrowing
    first'
    injection'
    headUnion
    injUnion
    freeVars
    overloadedVar
    overloaded
        | App_ _ freshTerms <- overloadedTerm =
            do
                OverloadSimplifier{resolveOverloading} <-
                    Simplifier.askOverloadSimplifier
                let second' =
                        resolveOverloading injUnion headUnion freshTerms
                return
                    Narrowing
                        { narrowingSubst =
                            Condition.assign (inject overloadedVar) narrowingTerm
                        , narrowingVars =
                            Attribute.getFreeElementVariables $ freeVariables narrowingTerm
                        , overloadPair = Pair (mkInj' first') (mkInj' second')
                        }
        | otherwise = error "This should not happen"
      where
        InjectedOverload{overload, injectionHead} = overloaded
        allVars = Attribute.freeVariable (inject overloadedVar) <> freeVars
        overloadedTerm = freshSymbolInstance allVars overload "x"
        mkInj' = maybeMkInj injection'
        narrowingTerm = maybeMkInj injectionHead overloadedTerm

-- | Generates fresh variables as arguments for a symbol to create a pattern.
freshSymbolInstance ::
    FreeVariables RewritingVariableName ->
    Symbol ->
    Text ->
    TermLike RewritingVariableName
freshSymbolInstance freeVars sym base =
    mkApplySymbol sym varTerms
        & refreshVariables freeVars
  where
    sorts = applicationSortsOperands $ symbolSorts sym
    varTerms = mkElemVar <$> zipWith mkVariable [1 ..] sorts

    mkVariable :: Integer -> Sort -> ElementVariable RewritingVariableName
    mkVariable vIdx vSort =
        mkElementVariable
            (generatedId $ base <> (Text.pack . show) vIdx)
            vSort
            & (fmap . fmap) mkConfigVariable

mkInj ::
    Inj () ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
mkInj inj injChild = (synthesize . InjF) inj{injChild}

maybeMkInj ::
    Maybe (Inj ()) ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
maybeMkInj maybeInj injChild = maybe injChild (flip mkInj injChild) maybeInj

notUnifiableError ::
    Monad unifier => TermLike RewritingVariableName -> OverloadingResult unifier a
notUnifiableError (DV_ _ _) = throwBottom "injected domain value"
notUnifiableError (InternalBool_ _) = throwBottom "injected builtin bool"
notUnifiableError (InternalInt_ _) = throwBottom "injected builtin int"
notUnifiableError (InternalList_ _) = throwBottom "injected builtin list"
notUnifiableError (InternalMap_ _) = throwBottom "injected builtin map"
notUnifiableError (InternalSet_ _) = throwBottom "injected builtin set"
notUnifiableError (InternalString_ _) = throwBottom "injected builtin string"
notUnifiableError _ = notApplicable

notUnifiableOverloads :: Monad unifier => OverloadingResult unifier a
notUnifiableOverloads = throwBottom "overloaded constructors not unifiable"
