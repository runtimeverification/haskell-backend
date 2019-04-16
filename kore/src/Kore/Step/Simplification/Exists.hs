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

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Debug.Trace

import           Control.Applicative
                 ( Alternative ((<|>)) )
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
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
    exists@Exists { existsVariable = variable, existsChild = child }
  =
    Debug.Trace.trace (unlines ["Exists.simplify:", show exists])
    $ do
    r <- simplifyEvaluated
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        variable
        child
    Debug.Trace.trace (unlines ["Exists.simplify/result:", show r]) (return r)

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
            (ExpandedPattern.topOf patternSort)
                { term =
                    mkExists variable
                    $ Maybe.fromMaybe (mkTop patternSort)
                    $ mkAndMaybe (Just term)
                    $ Predicate.fromPredicate patternSort <$> boundCondition
                }
          | otherwise =
            (ExpandedPattern.topOf patternSort)
                { term = term
                , predicate =
                    Predicate.makeAndPredicate freePredicate
                    $ Predicate.makeExistsPredicate variable
                    $ Maybe.fromMaybe Predicate.makeTruePredicate boundCondition
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
        mkAndMaybe a b = (mkAnd <$> a <*> b) <|> a <|> b
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
