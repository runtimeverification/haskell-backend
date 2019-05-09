{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
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
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier,
                 simplifyTerm, termLikeSimplifier )
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
import qualified Kore.Syntax.PatternF as Syntax
import           Kore.Unparser
import           Kore.Variables.Fresh

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a TermLike variable, returning an
'Pattern'.
-}
simplify
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier (Pattern variable)
simplify tools substitutionSimplifier axiomIdToEvaluator patt = do
    orPatt <- simplifyToOr tools axiomIdToEvaluator substitutionSimplifier patt
    return (OrPattern.toPattern orPatt)

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSimplifier
    -> TermLike variable
    -> Simplifier (OrPattern variable)
simplifyToOr tools axiomIdToEvaluator substitutionSimplifier patt =
    simplifyInternal
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        (Recursive.project patt)
  where
    simplifier = termLikeSimplifier
        (simplifyToOr tools axiomIdToEvaluator)

simplifyInternal
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Recursive.Base (TermLike variable) (TermLike variable)
    -> Simplifier (OrPattern variable)
simplifyInternal
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (valid :< patt)
  = do
    halfSimplified <- traverse simplifyTerm' patt
    -- TODO: Remove fst
    case halfSimplified of
        Syntax.AndF p ->
            And.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.ApplicationF p ->
            --  TODO: Re-evaluate outside of the application and stop passing
            -- the simplifier.
            Application.simplify
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (valid :< p)
        Syntax.BottomF p -> return $ Bottom.simplify p
        Syntax.CeilF p ->
            Ceil.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.DomainValueF p -> return $ DomainValue.simplify tools p
        Syntax.EqualsF p ->
            Equals.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.ExistsF p ->
            Exists.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.FloorF p -> return $ Floor.simplify p
        Syntax.ForallF p -> return $ Forall.simplify p
        Syntax.IffF p ->
            Iff.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.ImpliesF p ->
            Implies.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.InF p ->
            In.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.InhabitantF s -> return $ Inhabitant.simplify s
        -- TODO(virgil): Move next up through patterns.
        Syntax.NextF p -> return $ Next.simplify p
        Syntax.NotF p ->
            Not.simplify
                tools substitutionSimplifier simplifier axiomIdToEvaluator p
        Syntax.OrF p -> return $ Or.simplify p
        Syntax.RewritesF p -> return $ Rewrites.simplify p
        Syntax.StringLiteralF p -> return $ StringLiteral.simplify p
        Syntax.CharLiteralF p -> return $ CharLiteral.simplify p
        Syntax.TopF p -> return $ Top.simplify p
        Syntax.VariableF p -> return $ Variable.simplify p
        Syntax.SetVariableF p -> return $ SetVariable.simplify p
  where
    simplifyTerm' = simplifyTerm simplifier substitutionSimplifier
