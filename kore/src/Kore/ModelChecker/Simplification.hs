{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Simplification
    ( checkImplicationIsTop
    ) where

import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Conditional (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.TermLike
                 ( TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser
import           Kore.Variables.Fresh

checkImplicationIsTop
    :: SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> CommonExpandedPattern Object
    -> TermLike Variable
    -> Simplifier Bool
checkImplicationIsTop
    tools
    predicateSimplifier
    patternSimplifier
    axiomSimplifers
    lhs
    rhs
  = case (stripForallQuantifiers rhs) of
        ( forallQuantifiers, Implies_ _ implicationLHS implicationRHS ) -> do
            let rename = refreshVariables lhsFreeVariables forallQuantifiers
                subst = mkVar <$> rename
                implicationLHS' = TermLike.substitute subst implicationLHS
                implicationRHS' = TermLike.substitute subst implicationRHS
                resultTerm = mkCeil_
                                (mkAnd
                                    (mkAnd lhsMLPatt implicationLHS')
                                    (mkNot implicationRHS')
                                )
                result = Conditional
                            { term = resultTerm, predicate = Predicate.makeTruePredicate, substitution = mempty}
            (orResult, _) <- ExpandedPattern.simplify
                                tools
                                predicateSimplifier
                                patternSimplifier
                                axiomSimplifers
                                result
            return (isBottom orResult)
        _ -> (error . show . Pretty.vsep)
             [ "Not implemented error:"
             , "We don't know how to simplify the implication whose rhs is:"
             , Pretty.indent 4 (unparse rhs)
             ]
      where
        lhsFreeVariables = ExpandedPattern.freeVariables lhs
        lhsMLPatt = ExpandedPattern.toMLPattern lhs

stripForallQuantifiers
    :: TermLike Variable
    -> (Set.Set (Variable Object), TermLike Variable)
stripForallQuantifiers patt
  = case patt of
        Forall_ _ forallVar child ->
            let
                ( childVars, strippedChild ) = stripForallQuantifiers child
            in
                ( Set.insert forallVar childVars, strippedChild)
        _ -> ( Set.empty , patt )
