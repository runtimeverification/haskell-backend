{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    ) where

import qualified Data.Functor.Foldable as Recursive

import qualified Kore.AST.Common as Common
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( toExpandedPattern )
import qualified Kore.Step.Simplification.And as And
                 ( simplify )
import qualified Kore.Step.Simplification.Application as Application
                 ( simplify )
import qualified Kore.Step.Simplification.Bottom as Bottom
                 ( simplify )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( simplify )
import qualified Kore.Step.Simplification.CharLiteral as CharLiteral
                 ( simplify )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier, simplifyTerm,
                 stepPatternSimplifier )
import qualified Kore.Step.Simplification.DomainValue as DomainValue
                 ( simplify )
import qualified Kore.Step.Simplification.Equals as Equals
                 ( simplify )
import qualified Kore.Step.Simplification.Exists as Exists
                 ( simplify )
import qualified Kore.Step.Simplification.Floor as Floor
                 ( simplify )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( simplify )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( simplify )
import qualified Kore.Step.Simplification.Implies as Implies
                 ( simplify )
import qualified Kore.Step.Simplification.In as In
                 ( simplify )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant
                 ( simplify )
import qualified Kore.Step.Simplification.Next as Next
                 ( simplify )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplify )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplify )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
                 ( simplify )
import qualified Kore.Step.Simplification.SetVariable as SetVariable
                 ( simplify )
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
                 ( simplify )
import qualified Kore.Step.Simplification.Top as Top
                 ( simplify )
import qualified Kore.Step.Simplification.Variable as Variable
                 ( simplify )
import           Kore.Step.TermLike
import           Kore.Unparser
import           Kore.Variables.Fresh

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a TermLike variable, returning an
'Pattern'.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier
        ( Pattern level variable
        , SimplificationProof level
        )
simplify tools substitutionSimplifier axiomIdToEvaluator patt = do
    (orPatt, proof) <-
        simplifyToOr tools axiomIdToEvaluator substitutionSimplifier patt
    return
        ( OrOfExpandedPattern.toExpandedPattern orPatt
        , proof
        )

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrOfExpandedPattern'.
-}
simplifyToOr
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitutionSimplifier level
    -> TermLike variable
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplifyToOr tools axiomIdToEvaluator substitutionSimplifier patt =
    simplifyInternal
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        (Recursive.project patt)
  where
    simplifier = stepPatternSimplifier
        (simplifyToOr tools axiomIdToEvaluator)

simplifyInternal
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Recursive.Base (TermLike variable) (TermLike variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplifyInternal
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (valid :< patt)
  = do
    halfSimplified <- traverse simplifyTerm' patt
    -- TODO: Remove fst
    case fmap fst halfSimplified of
        Common.AndPattern p ->
            And.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.ApplicationPattern p ->
            --  TODO: Re-evaluate outside of the application and stop passing
            -- the simplifier.
            Application.simplify
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (valid :< p)
        Common.BottomPattern p -> return $ Bottom.simplify p
        Common.CeilPattern p ->
            Ceil.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.DomainValuePattern p -> return $ DomainValue.simplify tools p
        Common.EqualsPattern p ->
            Equals.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.ExistsPattern p ->
            Exists.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.FloorPattern p -> return $ Floor.simplify p
        Common.ForallPattern p -> return $ Forall.simplify p
        Common.IffPattern p ->
            Iff.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.ImpliesPattern p ->
            Implies.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.InPattern p ->
            In.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.InhabitantPattern s -> return $ Inhabitant.simplify s
        -- TODO(virgil): Move next up through patterns.
        Common.NextPattern p -> return $ Next.simplify p
        Common.NotPattern p ->
            fmap withProof $ Not.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Common.OrPattern p -> return $ Or.simplify p
        Common.RewritesPattern p -> return $ Rewrites.simplify p
        Common.StringLiteralPattern p -> return $ StringLiteral.simplify p
        Common.CharLiteralPattern p -> return $ CharLiteral.simplify p
        Common.TopPattern p -> return $ Top.simplify p
        Common.VariablePattern p -> return $ Variable.simplify p
        Common.SetVariablePattern p -> return $ SetVariable.simplify p
  where
    simplifyTerm' = simplifyTerm simplifier substitutionSimplifier
    withProof a = (a, SimplificationProof)
