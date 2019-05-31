{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Simplification
    ( checkImplicationIsTop
    ) where

import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike as TermLike
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser
import           Kore.Variables.Fresh

checkImplicationIsTop
    :: PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Variable
    -> TermLike Variable
    -> Simplifier Bool
checkImplicationIsTop
    predicateSimplifier
    patternSimplifier
    axiomSimplifers
    lhs
    rhs
  = case stripForallQuantifiers rhs of
        ( forallQuantifiers, Implies_ _ implicationLHS implicationRHS ) -> do
            let rename = refreshVariables lhsFreeVariables forallQuantifiers
                subst = mkVar <$> rename
                implicationLHS' = TermLike.substitute subst implicationLHS
                implicationRHS' = TermLike.substitute subst implicationRHS
                resultTerm =
                    mkCeil_
                        (mkAnd
                            (mkAnd lhsMLPatt implicationLHS')
                            (mkNot implicationRHS')
                        )
                result = Conditional
                    { term = resultTerm
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
            tools <- Simplifier.askMetadataTools
            orResult <-
                Pattern.simplify
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
        lhsFreeVariables = Pattern.freeVariables lhs
        lhsMLPatt = Pattern.toTermLike lhs

stripForallQuantifiers
    :: TermLike Variable
    -> (Set.Set (Variable), TermLike Variable)
stripForallQuantifiers patt
  = case patt of
        Forall_ _ forallVar child ->
            let
                ( childVars, strippedChild ) = stripForallQuantifiers child
            in
                ( Set.insert forallVar childVars, strippedChild)
        _ -> ( Set.empty , patt )
