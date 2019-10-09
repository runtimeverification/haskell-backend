{-|
Module      : Kore.Step.Axiom.Matcher
Description : Matches free-form patterns which can be used when applying
              Equals rules.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.Matcher
    ( MatchingVariable
    , matchIncremental
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Control.Error as Error
import Control.Lens
    ( (%=)
    , (.=)
    , (<>=)
    )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Control.Monad.State.Strict
    ( MonadState
    , StateT
    )
import qualified Control.Monad.State.Strict as Monad.State
import qualified Control.Monad.Trans as Monad.Trans
import Control.Monad.Trans.Maybe
    ( MaybeT (..)
    )
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Generics.Product
import Data.Map
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Sequence
    ( pattern (:<|)
    , pattern (:|>)
    , Seq
    )
import qualified Data.Sequence as Seq
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.List as List
import qualified Kore.Domain.Builtin as Builtin
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike hiding
    ( substitute
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.Simplification.AndTerms
    ( SortInjectionMatch (SortInjectionMatch)
    , simplifySortInjections
    )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionMatch
    ( SortInjectionMatch (..)
    )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionSimplification
    ( SortInjectionSimplification (..)
    )
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Error
    ( unsupportedPatterns
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
import Kore.Variables.Binding
import Kore.Variables.Fresh
    ( FreshVariable
    )
import qualified Kore.Variables.Fresh as Variables
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

-- * Matching

{- | Dispatch a single matching constraint.

@matchOne@ is the heart of the matching algorithm. Each matcher is applied to
the constraint in sequence, until one accepts the pair. The matchers may
introduce substitutions and new constraints. If none of the matchers accepts the
pair, it is deferred until we have more information.

 -}
matchOne
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MatcherT variable unifier ()
matchOne pair =
    (   matchVariable    pair
    <|> matchEqualHeads  pair
    <|> matchExists      pair
    <|> matchForall      pair
    <|> matchApplication pair
    <|> matchBuiltinList pair
    <|> matchBuiltinMap  pair
    <|> matchBuiltinSet  pair
    )
    & Error.maybeT (defer pair) return

{- | Drive @matchOne@ until it cannot continue.

Matching ends when all constraints have been dispatched. If there are remaining
deferred constraints, then matching fails.

 -}
matchIncremental
    :: forall variable unifier
    .  (MatchingVariable variable, MonadUnify unifier)
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
matchIncremental termLike1 termLike2 =
    Monad.State.evalStateT matcher initial
  where
    matcher = pop >>= maybe done (\pair -> matchOne pair >> matcher)

    initial =
        MatcherState
            { queued = Seq.singleton (Pair termLike1 termLike2)
            , deferred = empty
            , predicate = empty
            , substitution = mempty
            , bound = mempty
            , targets = free1
            , avoiding = free1 <> free2
            }
    free1 = (getFreeVariables . TermLike.freeVariables) termLike1
    free2 = (getFreeVariables . TermLike.freeVariables) termLike2

    -- | Check that matching is finished and construct the result.
    done :: MatcherT variable unifier (Predicate variable)
    done = do
        final@MatcherState { queued, deferred } <- Monad.State.get
        let isDone = null queued && null deferred
        Monad.unless isDone throwUnknown
        let MatcherState { predicate, substitution } = final
            predicate' =
                Predicate.fromPredicate
                $ MultiAnd.toPredicate predicate
            substitution' =
                Predicate.fromSubstitution
                $ Substitution.fromMap substitution
            solution = predicate' <> substitution'
        return solution

    throwUnknown =
        Monad.Trans.lift
        $ Monad.Unify.throwUnificationError
        $ unsupportedPatterns "Unknown match case" termLike1 termLike2

matchEqualHeads
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
-- Terminal patterns
matchEqualHeads (Pair (StringLiteral_ string1) (StringLiteral_ string2)) =
    Monad.guard (string1 == string2)
matchEqualHeads (Pair (BuiltinInt_ int1) (BuiltinInt_ int2)) =
    Monad.guard (int1 == int2)
matchEqualHeads (Pair (BuiltinBool_ bool1) (BuiltinBool_ bool2)) =
    Monad.guard (bool1 == bool2)
matchEqualHeads (Pair (BuiltinString_ string1) (BuiltinString_ string2)) =
    Monad.guard (string1 == string2)
matchEqualHeads (Pair (Bottom_ _) (Bottom_ _)) =
    return ()
matchEqualHeads (Pair (Top_ _) (Top_ _)) =
    return ()
-- Non-terminal patterns
matchEqualHeads (Pair (Ceil_ _ _ term1) (Ceil_ _ _ term2)) =
    push (Pair term1 term2)
matchEqualHeads (Pair (DV_ sort1 dv1) (DV_ sort2 dv2)) = do
    Monad.guard (sort1 == sort2)
    push (Pair dv1 dv2)
matchEqualHeads (Pair (Equals_ _ _ term11 term12) (Equals_ _ _ term21 term22)) =
    push (Pair term11 term21) >> push (Pair term12 term22)
matchEqualHeads _ = empty

matchExists
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchExists (Pair (Exists_ _ variable1 term1) (Exists_ _ variable2 term2)) =
    matchBinder (Binder variable1 term1) (Binder variable2 term2)
matchExists _ = empty

matchForall
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchForall (Pair (Forall_ _ variable1 term1) (Forall_ _ variable2 term2)) =
    matchBinder (Binder variable1 term1) (Binder variable2 term2)
matchForall _ = empty

matchBinder
    :: (MatchingVariable variable, MonadUnify unifier)
    => Binder (ElementVariable variable) (TermLike variable)
    -> Binder (ElementVariable variable) (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchBinder (Binder variable1 term1) (Binder variable2 term2) = do
    Monad.guard (variableSort1 == variableSort2)
    -- Lift the bound variable to the top level.
    lifted1 <- liftVariable unified1
    let term1' = fromMaybe term1 $ do
            subst1 <- Map.singleton unified1 . mkVar <$> lifted1
            return $ substituteTermLike subst1 term1
    let variable1' = fromMaybe unified1 lifted1
        subst2 = Map.singleton unified2 (mkVar variable1')
        term2' = substituteTermLike subst2 term2
    -- Record the uniquely-named variable so it will not be shadowed later.
    bindVariable variable1'
    push (Pair term1' term2')
  where
    unified1 = ElemVar variable1
    unified2 = ElemVar variable2
    elementVariableSort = sortedVariableSort . getElementVariable
    variableSort1 = elementVariableSort variable1
    variableSort2 = elementVariableSort variable2

matchVariable
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchVariable (Pair (Var_ variable1) (Var_ variable2))
  | variable1 == variable2 = return ()
matchVariable (Pair (ElemVar_ variable1) term2) = do
    targetCheck (ElemVar variable1)
    Monad.guard (isFunctionPattern term2)
    substitute variable1 term2
matchVariable (Pair (SetVar_ variable1) term2) = do
    targetCheck (SetVar variable1)
    setSubstitute variable1 term2
matchVariable _ = empty

matchApplication
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchApplication
    (Pair term1@(App_ symbol1 children1) term2@(App_ symbol2 children2))

  -- Match identical symbols.
  | symbol1 == symbol2 =
    Foldable.traverse_ push (zipWith Pair children1 children2)

  -- Match conformable sort injections.
  | otherwise = do
    Monad.guard (sort1 == sort2)
    tools <- Simplifier.askMetadataTools
    case simplifySortInjections tools term1 term2 of
        Just (SortInjectionSimplification.Matching injMatch) -> do
            let SortInjectionMatch { firstChild, secondChild } = injMatch
            push (Pair firstChild secondChild)
        _ -> empty
  where
    sort1 = termLikeSort term1
    sort2 = termLikeSort term2
matchApplication _ = empty

matchBuiltinList
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchBuiltinList (Pair (BuiltinList_ list1) (BuiltinList_ list2)) = do
    (aligned, tail2) <- leftAlignLists list1 list2 & Error.hoistMaybe
    Monad.guard (null tail2)
    Foldable.traverse_ push aligned
matchBuiltinList (Pair (App_ symbol1 children1) (BuiltinList_ list2))
  | List.isSymbolConcat symbol1 = matchBuiltinListConcat children1 list2
matchBuiltinList _ = empty

matchBuiltinListConcat
    :: (MatchingVariable variable, MonadUnify unifier)
    => [TermLike variable]
    -> Builtin.InternalList (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()

matchBuiltinListConcat [BuiltinList_ list1, frame1] list2 = do
    (aligned, tail2) <- leftAlignLists list1 list2 & Error.hoistMaybe
    Foldable.traverse_ push aligned
    push (Pair frame1 (mkBuiltinList tail2))

matchBuiltinListConcat [frame1, BuiltinList_ list1] list2 = do
    (head2, aligned) <- rightAlignLists list1 list2 & Error.hoistMaybe
    push (Pair frame1 (mkBuiltinList head2))
    Foldable.traverse_ push aligned

matchBuiltinListConcat _ _ = empty

matchBuiltinSet
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchBuiltinSet (Pair (BuiltinSet_ set1) (BuiltinSet_ set2)) = do
    matchNormalizedAc pushSetValue wrapTermLike normalized1 normalized2
  where
    normalized1 = Builtin.unwrapAc $ Builtin.builtinAcChild set1
    normalized2 = Builtin.unwrapAc $ Builtin.builtinAcChild set2
    pushSetValue _ = return ()
    wrapTermLike unwrapped =
        set2
        & Lens.set (field @"builtinAcChild") (Builtin.wrapAc unwrapped)
        & mkBuiltinSet
matchBuiltinSet _ = empty

matchBuiltinMap
    :: (MatchingVariable variable, MonadUnify unifier)
    => Pair (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchBuiltinMap (Pair (BuiltinMap_ map1) (BuiltinMap_ map2)) =
    matchNormalizedAc pushMapValue wrapTermLike normalized1 normalized2
  where
    normalized1 = Builtin.unwrapAc $ Builtin.builtinAcChild map1
    normalized2 = Builtin.unwrapAc $ Builtin.builtinAcChild map2
    pushMapValue = push . fmap Builtin.getMapValue
    wrapTermLike unwrapped =
        map2
        & Lens.set (field @"builtinAcChild") (Builtin.wrapAc unwrapped)
        & mkBuiltinMap
matchBuiltinMap _ = empty

-- * Implementation

type MatchingVariable variable = SimplifierVariable variable

{- | A matching constraint is a @Pair@ of patterns.

The first pattern will be made to match the second.

 -}
data Pair a = Pair !a !a
    deriving (Foldable, Functor)

{- | The internal state of the matching algorithm.
 -}
data MatcherState variable =
    MatcherState
        { queued :: !(Seq (Pair (TermLike variable)))
        -- ^ Solvable matching constraints.
        , deferred :: !(Seq (Pair (TermLike variable)))
        -- ^ Unsolvable matching constraints; may become solvable with more
        -- information.
        , substitution :: !(Map (UnifiedVariable variable) (TermLike variable))
        -- ^ Matching solution: Substitutions for target variables.
        , predicate :: !(MultiAnd (Syntax.Predicate variable))
        -- ^ Matching solution: Additional constraints.
        , bound :: !(Set (UnifiedVariable variable))
        -- ^ Bound variable that must not escape in the solution.
        , targets :: !(Set (UnifiedVariable variable))
        -- ^ Target variables that may be substituted.
        , avoiding :: !(Set (UnifiedVariable variable))
        -- ^ Variables that must not be shadowed.
        }
    deriving (GHC.Generic)

type MatcherT variable unifier = StateT (MatcherState variable) unifier

{- | Pop the next constraint from the matching queue.
 -}
pop
    :: MonadState (MatcherState variable) matcher
    => matcher (Maybe (Pair (TermLike variable)))
pop =
    Lens.use (field @"queued") >>= \case
        next :<| queued' -> do
            field @"queued" .= queued'
            return (Just next)
        _ ->
            return Nothing

{- | Push a new constraint onto the matching queue.
 -}
push
    :: MonadState (MatcherState variable) matcher
    => Pair (TermLike variable)
    -> matcher ()
push pair = field @"queued" %= (pair :<|)

{- | Defer a constraint until more information is available.

The constraint will be retried after the next substitution which affects it.

 -}
defer
    :: MonadState (MatcherState variable) matcher
    => Pair (TermLike variable)
    -> matcher ()
defer pair = field @"deferred" %= (:|> pair)

{- | Record an element substitution in the matching solution.

The substitution is applied to the remaining constraints and to the partial
matching solution (so that it is always normalized). @substitute@ ensures that:

1. The variable does not occur on the right-hand side.
2. No bound variable would escape through the right-hand side.
3. The right-hand side is defined (through a constraint, if necessary).

 -}
substitute
    :: (MatchingVariable variable, MonadUnify unifier)
    => ElementVariable variable
    -> TermLike variable
    -> MaybeT (MatcherT variable unifier) ()
substitute eVariable termLike = do
    -- Ensure that the variable does not occur free in the TermLike.
    occursCheck variable termLike
    -- Ensure that no bound variable would escape.
    escapeCheck termLike
    -- Ensure that the TermLike is defined.
    definedTerm termLike
    -- Record the substitution.
    field @"substitution" <>= Map.singleton variable termLike

    -- Isolate the deferred pairs which depend on the variable.
    -- After substitution, the dependent pairs go to the front of the queue.
    MatcherState { deferred } <- Monad.State.get
    let (indep, dep) = Seq.partition isIndependent deferred
    field @"deferred" .= indep

    -- Push the dependent deferred pairs to the front of the queue.
    Foldable.traverse_ push dep
    -- Apply the substitution to the queued pairs.
    field @"queued" . Lens.mapped %= substitute2

    -- Apply the substitution to the accumulated matching solution.
    field @"substitution" . Lens.mapped %= substitute1
    field @"predicate" . Lens.mapped %= Syntax.Predicate.substitute subst

    return ()
  where
    variable = ElemVar eVariable
    isIndependent = not . any (hasFreeVariable variable)
    subst = Map.singleton variable termLike
    substitute2 = fmap substitute1
    substitute1 = Builtin.renormalize . TermLike.substitute subst

{- | Record a set substitution in the matching solution.

The substitution is applied to the remaining constraints and to the partial
matching solution (so that it is always normalized). @substitute@ ensures that
the variable does not occur on the right-hand side of the substitution.

 -}
setSubstitute
    :: (MatchingVariable variable, MonadUnify unifier)
    => SetVariable variable
    -> TermLike variable
    -> MaybeT (MatcherT variable unifier) ()
setSubstitute sVariable termLike = do
    -- Ensure that the variable does not occur free in the TermLike.
    occursCheck variable termLike
    -- Record the substitution.
    field @"substitution" <>= Map.singleton variable termLike

    -- Isolate the deferred pairs which depend on the variable.
    -- After substitution, the dependent pairs go to the front of the queue.
    MatcherState { deferred } <- Monad.State.get
    let (indep, dep) = Seq.partition isIndependent deferred
    field @"deferred" .= indep

    -- Push the dependent deferred pairs to the front of the queue.
    Foldable.traverse_ push dep
    -- Apply the substitution to the queued pairs.
    field @"queued" . Lens.mapped %= substitute2

    -- Apply the substitution to the accumulated matching solution.
    field @"substitution" . Lens.mapped %= substitute1
    field @"predicate" . Lens.mapped %= Syntax.Predicate.substitute subst

    return ()
  where
    variable = SetVar sVariable
    isIndependent = not . any (hasFreeVariable variable)
    subst = Map.singleton variable termLike
    substitute2 = fmap substitute1
    substitute1 = substituteTermLike subst

substituteTermLike
    :: MatchingVariable variable
    => (Show variable, Unparse variable)
    => Map (UnifiedVariable variable) (TermLike variable)
    -> TermLike variable
    -> TermLike variable
substituteTermLike subst = Builtin.renormalize . TermLike.substitute subst

occursCheck
    :: (MatchingVariable variable, MonadUnify unifier)
    => UnifiedVariable variable
    -> TermLike variable
    -> MaybeT (MatcherT variable unifier) ()
occursCheck variable termLike =
    (Monad.guard . not) (hasFreeVariable variable termLike)

definedTerm
    :: (MatchingVariable variable, MonadState (MatcherState variable) matcher)
    => TermLike variable
    -> matcher ()
definedTerm termLike
  | isDefinedPattern termLike = return ()
  | otherwise = field @"predicate" <>= definedTermLike
  where
    definedTermLike = MultiAnd.make [makeCeilPredicate termLike]

{- | Ensure that the given variable is a target variable.

Matching should only produce substitutions for variables in one argument; these
are the "target" variables. After one or more substitutions, the first argument
can also contain non-target variables and this guard is used to ensure that we
do not attempt to match on them.

 -}
targetCheck
    :: (MatchingVariable variable, Monad unifier)
    => UnifiedVariable variable
    -> MaybeT (MatcherT variable unifier) ()
targetCheck variable = do
    MatcherState { targets } <- Monad.State.get
    Monad.guard (Set.member variable targets)

{- | Ensure that no bound variables occur free in the pattern.

We must not produce a matching solution which would allow a bound variable to
escape.

 -}
escapeCheck
    :: (MatchingVariable variable, Monad unifier)
    => TermLike variable
    -> MaybeT (MatcherT variable unifier) ()
escapeCheck termLike = do
    let free = getFreeVariables (TermLike.freeVariables termLike)
    MatcherState { bound } <- Monad.State.get
    Monad.guard (Set.disjoint bound free)

{- | Record the bound variable.

The bound variable will not escape, nor will it be shadowed.

 -}
bindVariable
    :: Ord variable
    => MonadState (MatcherState variable) matcher
    => UnifiedVariable variable
    -> matcher ()
bindVariable variable = do
    field @"bound" %= Set.insert variable
    field @"avoiding" %= Set.insert variable

{- | Lift a (bound) variable to the top level by with a globally-unique name.

Returns 'Nothing' if the variable name is already globally-unique.

 -}
liftVariable
    :: FreshVariable variable
    => MonadState (MatcherState variable) matcher
    => UnifiedVariable variable
    -> matcher (Maybe (UnifiedVariable variable))
liftVariable variable =
    flip Variables.refreshVariable variable <$> Lens.use (field @"avoiding")

leftAlignLists
    ::  Builtin.InternalList (TermLike variable)
    ->  Builtin.InternalList (TermLike variable)
    ->  Maybe
            ( Builtin.InternalList (Pair (TermLike variable))
            , Builtin.InternalList (TermLike variable)
            )
leftAlignLists internal1 internal2
  | length list2 < length list1 = empty
  | otherwise =
    return
        ( internal1 { Builtin.builtinListChild = list12 }
        , internal1 { Builtin.builtinListChild = tail2 }
        )
  where
    list1 = Builtin.builtinListChild internal1
    list2 = Builtin.builtinListChild internal2
    list12 = Seq.zipWith Pair list1 head2
    (head2, tail2) = Seq.splitAt (length list1) list2

rightAlignLists
    ::  Builtin.InternalList (TermLike variable)
    ->  Builtin.InternalList (TermLike variable)
    ->  Maybe
            ( Builtin.InternalList (TermLike variable)
            , Builtin.InternalList (Pair (TermLike variable))
            )
rightAlignLists internal1 internal2
  | length list2 < length list1 = empty
  | otherwise =
    return
        ( internal1 { Builtin.builtinListChild = head2 }
        , internal1 { Builtin.builtinListChild = list12 }
        )
  where
    list1 = Builtin.builtinListChild internal1
    list2 = Builtin.builtinListChild internal2
    list12 = Seq.zipWith Pair list1 tail2
    (head2, tail2) = Seq.splitAt (length list2 - length list1) list2

matchNormalizedAc
    :: (MatchingVariable variable, MonadUnify unifier)
    => (Pair (Builtin.Value normalized (TermLike variable)) -> MatcherT variable unifier ())
    ->  (Builtin.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
        -> TermLike variable
        )
    -> Builtin.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
    -> Builtin.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
    -> MaybeT (MatcherT variable unifier) ()
matchNormalizedAc pushValue wrapTermLike normalized1 normalized2
  | [] <- abstract2, [] <- opaque2
  , [] <- abstract1
  = do
    Monad.guard (null excess1)
    case opaque1 of
        []       -> Monad.guard (null excess2)
        [frame1] -> push (Pair frame1 normalized2')
        _        -> empty
    Monad.Trans.lift $ Foldable.traverse_ pushValue concrete12
  where
    normalized2' =
        wrapTermLike normalized2 { Builtin.concreteElements = excess2 }
    abstract1 = Builtin.elementsWithVariables normalized1
    concrete1 = Builtin.concreteElements normalized1
    opaque1 = Builtin.opaque normalized1
    abstract2 = Builtin.elementsWithVariables normalized2
    concrete2 = Builtin.concreteElements normalized2
    opaque2 = Builtin.opaque normalized2
    excess1 = Map.difference concrete1 concrete2
    excess2 = Map.difference concrete2 concrete1
    concrete12 = Map.intersectionWith Pair concrete1 concrete2
matchNormalizedAc _ _ _ _ = empty
