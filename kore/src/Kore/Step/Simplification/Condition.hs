{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Condition
    ( create
    , simplify
    , simplifyPredicate
    , simplifyCondition
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
    ( field
    )
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( sortOn
    )

import Changed
import Kore.Attribute.Synthetic
    ( synthesize
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makePredicate
    , predicateSort
    , unwrapPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Symbol
    ( isConstructor
    , isFunction
    )
import Kore.Internal.TermLike
    ( pattern App_
    , pattern InternalBool_
    , pattern InternalString_
    , pattern Builtin_
    , pattern Equals_
    , pattern Exists_
    , pattern Forall_
    , pattern Inj_
    , pattern InternalBytes_
    , pattern InternalInt_
    , pattern Mu_
    , pattern Not_
    , pattern Nu_
    , TermLike
    , Variable (..)
    , mkBottom
    , mkTop
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unparser
import Logic
import Pair
import qualified Pretty

{- | Create a 'ConditionSimplifier' using 'simplify'.
-}
create
    :: MonadSimplify simplifier
    => SubstitutionSimplifier simplifier
    -> ConditionSimplifier simplifier
create substitutionSimplifier =
    ConditionSimplifier $ simplify substitutionSimplifier

{- | Simplify a 'Condition'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified until it stabilizes.

The 'term' of 'Conditional' may be any type; it passes through @simplify@
unmodified.
-}
simplify
    ::  forall simplifier variable any
    .   ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  SubstitutionSimplifier simplifier
    ->  SideCondition variable
    ->  Conditional variable any
    ->  LogicT simplifier (Conditional variable any)
simplify SubstitutionSimplifier { simplifySubstitution } sideCondition =
    normalize >=> worker
  where
    worker Conditional { term, predicate, substitution } = do
        let substitution' = Substitution.toMap substitution
            predicate' = Predicate.substitute substitution' predicate
        simplified <- simplifyPredicate sideCondition predicate'
        TopBottom.guardAgainstBottom simplified
        let merged = simplified <> Condition.fromSubstitution substitution
        normalized <- normalize merged
        -- Check for full simplification *after* normalization. Simplification
        -- may have produced irrelevant substitutions that become relevant after
        -- normalization.
        let simplifiedPattern =
                Lens.traverseOf
                    (field @"predicate")
                    simplifyConjunctions
                    normalized { term }
        if fullySimplified simplifiedPattern
            then return (extract simplifiedPattern)
            else worker (extract simplifiedPattern)

    -- TODO(Ana): this should also check if the predicate is simplified
    fullySimplified (Unchanged Conditional { predicate, substitution }) =
        Predicate.isFreeOf predicate variables
      where
        variables = Substitution.variables substitution
    fullySimplified (Changed _) = False

    normalize
        ::  forall any'
        .   Conditional variable any'
        ->  LogicT simplifier (Conditional variable any')
    normalize conditional@Conditional { substitution } = do
        let conditional' = conditional { substitution = mempty }
        predicates' <- lift $
            simplifySubstitution sideCondition substitution
        predicate' <- scatter predicates'
        return $ Conditional.andCondition conditional' predicate'

{- | Simplify the 'Predicate' once.

@simplifyPredicate@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'

-}
simplifyPredicate
    ::  ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  SideCondition variable
    ->  Predicate variable
    ->  LogicT simplifier (Condition variable)
simplifyPredicate sideCondition predicate = do
    patternOr <-
        lift
        $ simplifyTermLike sideCondition
        $ unwrapPredicate predicate
    -- Despite using lift above, we do not need to
    -- explicitly check for \bottom because patternOr is an OrPattern.
    scatter (OrPattern.map eraseTerm patternOr)
  where
    eraseTerm conditional
      | TopBottom.isTop (Pattern.term conditional)
      = Conditional.withoutTerm conditional
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse conditional
            ]

simplifyConjunctions
    :: InternalVariable variable
    => Predicate variable
    -> Changed (Predicate variable)
simplifyConjunctions original@(MultiAnd.fromPredicate -> predicates) =
    let sort = predicateSort original
     in case simplifyConjunctionByAssumption predicates of
            Unchanged _ -> Unchanged original
            Changed changed ->
                Changed (MultiAnd.toPredicateSorted sort changed)

{- | Simplify the conjunction of 'Predicate' clauses by assuming each is true.
The conjunction is simplified by the identity:
@
A ∧ P(A) = A ∧ P(⊤)
@
 -}
simplifyConjunctionByAssumption
    :: forall variable
    .  InternalVariable variable
    => MultiAnd (Predicate variable)
    -> Changed (MultiAnd (Predicate variable))
simplifyConjunctionByAssumption (toList -> andPredicates) =
    fmap MultiAnd.make
    $ flip evalStateT HashMap.empty
    $ for (sortBySize andPredicates)
    $ \predicate' -> do
        let original = Predicate.unwrapPredicate predicate'
        result <- applyAssumptions original
        assume result
        return result
  where
    -- Sorting by size ensures that every clause is considered before any clause
    -- which could contain it, because the containing clause is necessarily
    -- larger.
    sortBySize :: [Predicate variable] -> [Predicate variable]
    sortBySize = sortOn (size . from)

    size :: TermLike variable -> Int
    size =
        Recursive.fold $ \(_ :< termLikeF) ->
            case termLikeF of
                TermLike.EvaluatedF evaluated -> TermLike.getEvaluated evaluated
                TermLike.DefinedF defined -> TermLike.getDefined defined
                _ -> 1 + sum termLikeF

    assume
        :: Predicate variable
        -> StateT (HashMap (TermLike variable) (TermLike variable)) Changed ()
    assume predicate1 =
        State.modify' (assumeEqualTerms . assumePredicate)
      where
        assumePredicate =
            case termLike of
                Not_ _ notChild ->
                    -- Infer that the predicate is \bottom.
                    HashMap.insert notChild (mkBottom sort)
                _ ->
                    -- Infer that the predicate is \top.
                    HashMap.insert termLike (mkTop sort)
        assumeEqualTerms =
            case retractLocalFunction termLike of
                Just (Pair term1 term2) -> HashMap.insert term1 term2
                _ -> id

        termLike = Predicate.unwrapPredicate predicate1
        sort = termLikeSort termLike

    applyAssumptions
        ::  TermLike variable
        ->  StateT (HashMap (TermLike variable) (TermLike variable)) Changed
                (Predicate variable)
    applyAssumptions replaceIn = do
        assumptions <- State.get
        lift $ fmap
            (unsafeMakePredicate assumptions replaceIn)
            (applyAssumptionsWorker assumptions replaceIn)

    unsafeMakePredicate replacements original result =
        case makePredicate result of
            -- TODO (ttuegel): https://github.com/kframework/kore/issues/1442
            -- should make it impossible to have an error here.
            Left err ->
                (error . show . Pretty.vsep . map (either id (Pretty.indent 4)))
                [ Left "Replacing"
                , Right (Pretty.vsep (unparse <$> HashMap.keys replacements))
                , Left "in"
                , Right (unparse original)
                , Right (Pretty.pretty err)
                ]
            Right p -> p

    applyAssumptionsWorker
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> Changed (TermLike variable)
    applyAssumptionsWorker assumptions original
      | Just result <- HashMap.lookup original assumptions = Changed result

      | HashMap.null assumptions' = Unchanged original

      | otherwise =
        traverse (applyAssumptionsWorker assumptions') replaceIn
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | Exists_ _ var _ <- original = restrictAssumptions (inject var)
          | Forall_ _ var _ <- original = restrictAssumptions (inject var)
          | Mu_       var _ <- original = restrictAssumptions (inject var)
          | Nu_       var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            HashMap.filterWithKey
                (\termLike _ -> wouldNotCapture termLike)
                assumptions
          where
            wouldNotCapture = not . TermLike.hasFreeVariable variableName

{- | Get a local function definition from a 'TermLike'.
A local function definition is a predicate that we can use to evaluate a
function locally (based on the side conditions) when none of the functions
global definitions (axioms) apply. We are looking for a 'TermLike' of the form
@
\equals(f(...), C(...))
@
where @f@ is a function and @C@ is a constructor, sort injection or builtin.
@retractLocalFunction@ will match an @\equals@ predicate with its arguments
in either order, but the function pattern is always returned first in the
'Pair'.
 -}
retractLocalFunction
    :: TermLike variable
    -> Maybe (Pair (TermLike variable))
retractLocalFunction =
    \case
        Equals_ _ _ term1 term2 -> go term1 term2 <|> go term2 term1
        _ -> Nothing
  where
    go term1@(App_ symbol1 _) term2
      | isFunction symbol1 =
        -- TODO (thomas.tuegel): Add tests.
        case term2 of
            App_ symbol2 _
              | isConstructor symbol2 -> Just (Pair term1 term2)
            Inj_ _     -> Just (Pair term1 term2)
            Builtin_ _ -> Just (Pair term1 term2)
            InternalInt_ _ -> Just (Pair term1 term2)
            InternalBytes_ _ _ -> Just (Pair term1 term2)
            InternalString_ _ -> Just (Pair term1 term2)
            InternalBool_ _ -> Just (Pair term1 term2)
            _          -> Nothing
    go _ _ = Nothing
