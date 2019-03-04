{-|
Module      : Kore.Step.Simplification.Pattern
Description : Tools for Pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Pattern
    ( simplify
    , simplifyToOr
    ) where

import           Kore.AST.MetaOrObject
import           Kore.AST.Pure
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( toExpandedPattern )
import           Kore.Step.Pattern
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
                 Simplifier, StepPatternSimplifier (..) )
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
import qualified Kore.Step.Simplification.Next as Next
                 ( simplify )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplify )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplify )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
                 ( simplify )
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
                 ( simplify )
import qualified Kore.Step.Simplification.Top as Top
                 ( simplify )
import qualified Kore.Step.Simplification.Variable as Variable
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
import           Kore.Variables.Fresh

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a StepPattern level variable, returning an
'ExpandedPattern'.
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
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> StepPattern level variable
    -> Simplifier
        ( ExpandedPattern level variable
        , SimplificationProof level
        )
simplify tools substitutionSimplifier axiomIdToEvaluator patt = do
    (orPatt, proof) <-
        simplifyToOr tools axiomIdToEvaluator substitutionSimplifier patt
    return
        ( OrOfExpandedPattern.toExpandedPattern orPatt
        , proof
        )

{-|'simplifyToOr' simplifies a StepPattern level variable, returning an
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
    => MetadataTools level StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitutionSimplifier level
    -> StepPattern level variable
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
        (fromPurePattern patt)
  where
    simplifier = StepPatternSimplifier
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
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Base (StepPattern level variable) (StepPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplifyInternal
    tools
    substitutionSimplifier
    simplifier@(StepPatternSimplifier unwrappedSimplifier)
    axiomIdToEvaluator
    (valid :< patt)
  = do
    halfSimplified <- traverse (unwrappedSimplifier substitutionSimplifier) patt
    -- TODO: Remove fst
    case fmap fst halfSimplified of
        AndPattern p ->
            And.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        ApplicationPattern p ->
            --  TODO: Re-evaluate outside of the application and stop passing
            -- the simplifier.
            Application.simplify
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (valid :< p)
        BottomPattern p -> return $ Bottom.simplify p
        CeilPattern p ->
            Ceil.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        DomainValuePattern p -> return $ DomainValue.simplify tools p
        EqualsPattern p ->
            Equals.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        ExistsPattern p ->
            Exists.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        FloorPattern p -> return $ Floor.simplify p
        ForallPattern p -> return $ Forall.simplify p
        IffPattern p -> return $ Iff.simplify p
        ImpliesPattern p -> return $ Implies.simplify p
        InPattern p ->
            In.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        -- TODO(virgil): Move next up through patterns.
        NextPattern p -> return $ Next.simplify p
        NotPattern p -> return $ Not.simplify p
        OrPattern p -> return $ Or.simplify p
        RewritesPattern p -> return $ Rewrites.simplify p
        StringLiteralPattern p -> return $ StringLiteral.simplify p
        CharLiteralPattern p -> return $ CharLiteral.simplify p
        TopPattern p -> return $ Top.simplify p
        VariablePattern p -> return $ Variable.simplify p
