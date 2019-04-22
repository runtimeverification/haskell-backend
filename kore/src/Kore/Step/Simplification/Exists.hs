{-|
Module      : Kore.Step.Simplification.Exists
Description : Tools for Exists pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Exists
    ( simplify
    , makeEvaluate
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Map.Strict as Map
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( traverseFlattenWithPairs )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue )
import qualified Kore.Step.Representation.Predicated as Predicated
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
                 ( BranchT, PredicateSubstitutionSimplifier,
                 SimplificationProof (..), Simplifier, StepPatternSimplifier,
                 gather, scatter )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Substitution as Substitution
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh


-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Exists' pattern with an 'OrOfExpandedPattern'
child.

The simplification of exists x . (pat and pred and subst) is equivalent to:

* If the subst contains an assignment for x, then substitute that in pat and
  pred, reevaluate them and return
  (reevaluated-pat and reevaluated-pred and subst-without-x).
* Otherwise, if x does not occur free in pat and pred, return
  (pat and pred and subst)
* Otherwise, if x does not occur free in pat, return
  (pat and (exists x . pred) and subst)
* Otherwise, if x does not occur free in pred, return
  ((exists x . pat) and pred and subst)
* Otherwise return
  ((exists x . pat and pred) and subst)
-}
simplify
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Exists level variable (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Exists { existsVariable = variable, existsChild = child }
  =
    simplifyEvaluated
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        variable
        child

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Exists level) (Valid level) (OrOfExpandedPattern level variable)

instead of a 'variable level' and an 'OrOfExpandedPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Valid' annotation will
eventually cache information besides the pattern sort, which will make it even
more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable level
    -> OrOfExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    simplified
  | OrOfExpandedPattern.isTrue simplified =
    return (simplified, SimplificationProof)
  | OrOfExpandedPattern.isFalse simplified =
    return (simplified, SimplificationProof)
  | otherwise = do
    (evaluated, _proofs) <-
        MultiOr.traverseFlattenWithPairs
            (makeEvaluate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                variable
            )
            simplified
    return ( evaluated, SimplificationProof )

{-| evaluates an 'Exists' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable level
    -> ExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    original
  = fmap withProof $ gather $ do
    normalized <- normalize original
    let Predicated { substitution = normalizedSubstitution } = normalized
    case splitSubstitution variable normalizedSubstitution of
        (Left boundTerm, freeSubstitution) ->
            makeEvaluateBoundLeft
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                variable
                boundTerm
                normalized { substitution = freeSubstitution }
        (Right boundSubstitution, freeSubstitution) ->
            makeEvaluateBoundRight
                variable
                freeSubstitution
                normalized { substitution = boundSubstitution }
  where
    withProof a = (a, SimplificationProof)
    normalize =
        Substitution.normalize
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

{- | Existentially quantify a variable in the given 'ExpandedPattern'.

The variable was found on the left-hand side of a substitution and the given
term will be substituted everywhere. The variable may occur anywhere in the
'term' or 'predicate' of the 'ExpandedPattern', but not in the
'substitution'. The final result will not contain the quantified variable and
thus the quantifier will actually be omitted.

See also: 'quantifyExpandedPattern'

 -}
makeEvaluateBoundLeft
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable level  -- ^ quantified variable
    -> StepPattern level variable  -- ^ substituted term
    -> ExpandedPattern level variable
    -> BranchT Simplifier (ExpandedPattern level variable)
makeEvaluateBoundLeft
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    boundTerm
    normalized
  = do
        let
            boundSubstitution = Map.singleton variable boundTerm
            substituted =
                normalized
                    { term =
                        Pattern.substitute boundSubstitution
                        $ Predicated.term normalized
                    , predicate =
                        Predicate.substitute boundSubstitution
                        $ Predicated.predicate normalized
                    }
        (results, _proof) <- Monad.Trans.lift $ simplify' substituted
        scatter results
  where
    simplify' =
        ExpandedPattern.simplify
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

{- | Existentially quantify a variable in the given 'ExpandedPattern'.

The variable does not occur in the any equality in the free substitution. The
variable may occur anywhere in the 'term' or 'predicate' of the
'ExpandedPattern', but only on the right-hand side of an equality in the
'substitution'.

See also: 'quantifyExpandedPattern'

 -}
makeEvaluateBoundRight
    ::  ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => variable Object  -- ^ variable to be quantified
    -> Substitution Object variable  -- ^ free substitution
    -> ExpandedPattern Object variable  -- ^ pattern to quantify
    -> BranchT Simplifier (ExpandedPattern Object variable)
makeEvaluateBoundRight
    variable
    freeSubstitution
    normalized
  = do
    TopBottom.guardAgainstBottom simplifiedPattern
    return simplifiedPattern
  where
    simplifiedPattern =
        Predicated.andCondition
            (quantifyExpandedPattern variable normalized)
            (PredicateSubstitution.fromSubstitution freeSubstitution)

{- | Split the substitution on the given variable.

The substitution must be normalized and the normalization state is preserved.

The result is a pair of:

* Either the term bound to the variable (if the variable is on the 'Left' side
  of a substitution) or the substitutions that depend on the variable (if the
  variable is on the 'Right' side of a substitution). (These conditions are
  mutually exclusive for a normalized substitution.)
* The substitutions that do not depend on the variable at all.

 -}
splitSubstitution
    :: (HasCallStack, Ord (variable Object))
    => variable Object
    -> Substitution Object variable
    ->  ( Either (StepPattern Object variable) (Substitution Object variable)
        , Substitution Object variable
        )
splitSubstitution variable substitution =
    (bound, independent)
  where
    (dependent, independent) = Substitution.partition hasVariable substitution
    hasVariable variable' term =
        variable == variable' || Pattern.hasFreeVariable variable term
    bound =
        maybe (Right dependent) Left
        $ Map.lookup variable (Substitution.toMap dependent)

{- | Existentially quantify the variable an 'ExpandedPattern'.

The substitution is assumed to depend on the quantified variable. The quantifier
is lowered onto the 'term' or 'predicate' alone, or omitted, if possible.

 -}
quantifyExpandedPattern
    ::  ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => variable Object
    -> ExpandedPattern Object variable
    -> ExpandedPattern Object variable
quantifyExpandedPattern variable Predicated { term, predicate, substitution }
  | quantifyTerm, quantifyPredicate =
      Predicated
        { term =
            mkExists variable
            $ mkAnd term
            $ Predicate.unwrapPredicate predicate'
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }
  | quantifyTerm =
      Predicated
        { term = mkExists variable term
        , predicate
        , substitution
        }
  | quantifyPredicate =
      Predicated
        { term
        , predicate = Predicate.makeExistsPredicate variable predicate'
        , substitution = mempty
        }
  | otherwise = Predicated { term, predicate, substitution }
  where
    quantifyTerm = Pattern.hasFreeVariable variable term
    predicate' =
        Predicate.makeAndPredicate predicate
        $ Predicate.fromSubstitution substitution
    quantifyPredicate = Predicate.hasFreeVariable variable predicate'
