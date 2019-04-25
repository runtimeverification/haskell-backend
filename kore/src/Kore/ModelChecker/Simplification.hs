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
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
                 ( CommonStepPattern )
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser
import           Kore.Variables.Fresh

checkImplicationIsTop
    :: forall level . (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> CommonExpandedPattern level
    -> CommonStepPattern level
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
                implicationLHS' = Pattern.substitute subst implicationLHS
                implicationRHS' = Pattern.substitute subst implicationRHS
                resultTerm = mkCeil_
                                (mkAnd
                                    (mkAnd lhsMLPatt implicationLHS')
                                    (mkNot implicationRHS')
                                )
                result = Predicated
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
    :: CommonStepPattern level
    -> (Set.Set (Variable level), CommonStepPattern level)
stripForallQuantifiers patt
  = case patt of
        Forall_ _ forallVar child ->
            let
                ( childVars, strippedChild ) = stripForallQuantifiers child
            in
                ( Set.insert forallVar childVars, strippedChild)
        _ -> ( Set.empty , patt )
