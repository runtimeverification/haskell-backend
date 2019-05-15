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

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike as Pattern
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( BranchT, PredicateSimplifier, Simplifier,
                 TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather, scatter )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import qualified Kore.Step.Substitution as Substitution
import           Kore.Syntax.Exists
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh


-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Exists' pattern with an 'OrPattern'
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
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Exists Sort variable (OrPattern variable)
    -> Simplifier (OrPattern variable)
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

> CofreeF (Exists Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of a 'variable' and an 'OrPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Attribute.Pattern' annotation
will eventually cache information besides the pattern sort, which will make it
even more useful to carry around.

-}
simplifyEvaluated
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable
    -> OrPattern variable
    -> Simplifier (OrPattern variable)
simplifyEvaluated
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    simplified
  | OrPattern.isTrue simplified  = return simplified
  | OrPattern.isFalse simplified = return simplified
  | otherwise = do
    evaluated <-
        traverse
            (makeEvaluate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                variable
            )
            simplified
    return (OrPattern.flatten evaluated)

{-| evaluates an 'Exists' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable
    -> Pattern variable
    -> Simplifier (OrPattern variable)
makeEvaluate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    original
  = fmap OrPattern.fromPatterns $ BranchT.gather $ do
    normalized <- normalize original
    let Conditional { substitution = normalizedSubstitution } = normalized
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
    normalize =
        Substitution.normalize
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

{- | Existentially quantify a variable in the given 'Pattern'.

The variable was found on the left-hand side of a substitution and the given
term will be substituted everywhere. The variable may occur anywhere in the
'term' or 'predicate' of the 'Pattern', but not in the
'substitution'. The quantified variable must not occur free in the substituted
 term; an error is thrown if it is found.  The final result will not contain the
 quantified variable and thus the quantifier will actually be omitted.

See also: 'quantifyPattern'

 -}
makeEvaluateBoundLeft
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Simplifies patterns.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> variable  -- ^ quantified variable
    -> TermLike variable  -- ^ substituted term
    -> Pattern variable
    -> BranchT Simplifier (Pattern variable)
makeEvaluateBoundLeft
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    variable
    boundTerm
    normalized
  = withoutFreeVariable variable boundTerm $ do
        let
            boundSubstitution = Map.singleton variable boundTerm
            substituted =
                normalized
                    { term =
                        Pattern.substitute boundSubstitution
                        $ Conditional.term normalized
                    , predicate =
                        Syntax.Predicate.substitute boundSubstitution
                        $ Conditional.predicate normalized
                    }
        orPattern <- Monad.Trans.lift $ simplify' substituted
        BranchT.scatter (MultiOr.extractPatterns orPattern)
  where
    simplify' =
        Pattern.simplify
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

{- | Existentially quantify a variable in the given 'Pattern'.

The variable does not occur in the any equality in the free substitution. The
variable may occur anywhere in the 'term' or 'predicate' of the
'Pattern', but only on the right-hand side of an equality in the
'substitution'.

See also: 'quantifyPattern'

 -}
makeEvaluateBoundRight
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => variable  -- ^ variable to be quantified
    -> Substitution variable  -- ^ free substitution
    -> Pattern variable  -- ^ pattern to quantify
    -> BranchT Simplifier (Pattern variable)
makeEvaluateBoundRight
    variable
    freeSubstitution
    normalized
  = do
    TopBottom.guardAgainstBottom simplifiedPattern
    return simplifiedPattern
  where
    simplifiedPattern =
        Conditional.andCondition
            (quantifyPattern variable normalized)
            (Predicate.fromSubstitution freeSubstitution)

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
    :: (HasCallStack, Ord variable)
    => variable
    -> Substitution variable
    ->  ( Either (TermLike variable) (Substitution variable)
        , Substitution variable
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

{- | Existentially quantify the variable an 'Pattern'.

The substitution is assumed to depend on the quantified variable. The quantifier
is lowered onto the 'term' or 'predicate' alone, or omitted, if possible.

 -}
quantifyPattern
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => variable
    -> Pattern variable
    -> Pattern variable
quantifyPattern variable original@Conditional { term, predicate, substitution }
  | quantifyTerm, quantifyPredicate
  = Pattern.fromTermLike
    $ mkExists variable
    $ mkAnd term (Syntax.Predicate.unwrapPredicate predicate')
  | quantifyTerm = mkExists variable <$> original
  | quantifyPredicate =
    Conditional.withCondition term
    $ Predicate.fromPredicate
    $ Syntax.Predicate.makeExistsPredicate variable predicate'
  | otherwise = original
  where
    quantifyTerm = Pattern.hasFreeVariable variable term
    predicate' =
        Syntax.Predicate.makeAndPredicate predicate
        $ Syntax.Predicate.fromSubstitution substitution
    quantifyPredicate = Syntax.Predicate.hasFreeVariable variable predicate'
