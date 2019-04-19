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

import           Control.Applicative
                 ( Alternative ((<|>)) )
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate, makeTruePredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make, traverseFlattenWithPairs )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue )
import qualified Kore.Step.Representation.Predicated as Predicated
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
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
    patt@Predicated { term, predicate, substitution }
  =
    case boundSubstitution of
        Nothing ->
            return (makeEvaluateNoFreeVarInSubstitution variable patt)
        Just boundTerm -> do
            (substitutedPat, _proof) <-
                substituteTermPredicate
                    term
                    predicate
                    (Map.singleton variable boundTerm)
                    (Substitution.unsafeWrap $ Map.toList freeSubstitution)
            (result, _proof) <-
                ExpandedPattern.simplify
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    substitutedPat
            return (result , SimplificationProof)
  where
    (boundSubstitution, freeSubstitution) =
        splitSubstitutionByVariable variable $ Substitution.toMap substitution

{- | Existentially quantify a variable over an 'ExpandedPattern'.

The input is a pattern of the form

@
φ ∧ P ∧ S
@

where @P@ is a predicate and @S@ is a substitution, having the form

@
S = ∧ᵢ xᵢ = tᵢ
@

where @xᵢ@ is a variable. The quantified variable @y@ does not occur on the
left-hand side of any conjunct in @S@, but this is not checked. The quantifier
will be lowered into the pattern as far as possible.

The predicate @P@ is split into a bound part and a free part,

@
P = freeP ∧ boundP
@

such that @freeP@ does not contain @y@, but @boundP@ (if it exists) does contain
@y@. Likewise the substitution is split into a bound part and a free part,

@
S = freeS ∧ boundS
@

such that @y@ does not occur on the right-hand side of any conjunct in @freeS@,
but @y@ occurs on the right-hand side of /every/ conjunct in @boundS@.

If @y@ occurs in @φ@, the result is

@
(∃ y. φ ∧ boundP ∧ boundS) ∧ freeP ∧ freeS
@

otherwise (if @y@ does not occur in @φ@) the result is

@
φ ∧ (freeP ∧ (∃ y. boundP ∧ boundS)) ∧ freeS.
@

 -}
makeEvaluateNoFreeVarInSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        )
    => variable level
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNoFreeVarInSubstitution
    variable
    Predicated { term, predicate, substitution }
  =
    (MultiOr.make [simplifiedPattern], SimplificationProof)
  where
    hasVariable = Set.member variable
    simplifiedPattern =
        boundConfiguration `Predicated.andCondition` freeCondition
      where
        boundConfiguration
          | hasVariable (Pattern.freeVariables term) =
            -- Quantify the term (with bound variables) in conjunction with the
            -- conditions with bound variables.
            (ExpandedPattern.topOf patternSort)
                { term =
                    mkExists variable . mkAndMaybe term
                    $ Predicate.fromPredicate patternSort <$> boundCondition
                }
          | otherwise =
            -- Keep the term (free of bound variables) outside the quantifier on
            -- the conditions with bound variables.
            (ExpandedPattern.topOf patternSort)
                { term = term
                , predicate =
                    maybe
                        Predicate.makeTruePredicate
                        (Predicate.makeExistsPredicate variable)
                        boundCondition
                }
        Valid { patternSort } = extract term

        (boundPredicate, freePredicate)
          | hasVariable (Predicate.freeVariables predicate) =
            (Just predicate, makeTruePredicate)
          | otherwise = (Nothing, predicate)
        (boundSubstitution, freeSubstitution) =
            splitSubstitutionByDependency variable substitution

        boundCondition =
            mkAndPredicateMaybe boundPredicate
            $ Predicate.fromSubstitution <$> boundSubstitution
        freeCondition =
            Predicated
                { term = ()
                , predicate = freePredicate
                , substitution = freeSubstitution
                }

        mkAndMaybe a = maybe a (mkAnd a)
        mkAndPredicateMaybe a b =
            (Predicate.makeAndPredicate <$> a <*> b) <|> a <|> b

substituteTermPredicate
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => StepPattern level variable
    -> Predicate level variable
    -> Map (variable level) (StepPattern level variable)
    -> Substitution level variable
    -> Simplifier
        (ExpandedPattern level variable, SimplificationProof level)
substituteTermPredicate term predicate substitution globalSubstitution =
    return
        ( Predicated
            { term = substitute substitution term
            , predicate = substitute substitution <$> predicate
            , substitution = globalSubstitution
            }
        , SimplificationProof
        )

{- | Split the substitution on the given variable.

Returns the term associated to the variable in the substitution, if any, and the
remainder of the substitution without the variable.

 -}
splitSubstitutionByVariable
    :: Ord variable
    => variable
    -> Map variable term
    -> (Maybe term, Map variable term)
splitSubstitutionByVariable var subst =
    (Map.lookup var subst, Map.delete var subst)

{- | Split the substitution by dependency the given variable.

Returns the terms of the substitution with and without dependency on the given
variable, respectively.

 -}
splitSubstitutionByDependency
    :: Ord (variable level)
    => variable level
    -> Substitution level variable
    -> (Maybe (Substitution level variable), Substitution level variable)
splitSubstitutionByDependency variable substitution =
    (if Substitution.null with then Nothing else Just with, without)
  where
    (with, without) = Substitution.partition hasVariable substitution
    hasVariable (_, term) = Set.member variable (Pattern.freeVariables term)
