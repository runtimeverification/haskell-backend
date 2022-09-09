{-# LANGUAGE FlexibleInstances #-}

module Main (main, ingredients, tests) where

import System.Environment qualified as E
import Test.Data.Graph.TopologicalSort qualified
import Test.Data.InternedText qualified
import Test.Data.Limit qualified
import Test.Data.Sup qualified
import Test.Debug qualified
import Test.Injection qualified
import Test.Kore.AST.Common qualified
import Test.Kore.Attribute.Assoc qualified
import Test.Kore.Attribute.Axiom.Concrete qualified
import Test.Kore.Attribute.Axiom.Symbolic qualified
import Test.Kore.Attribute.Axiom.Unit qualified
import Test.Kore.Attribute.Comm qualified
import Test.Kore.Attribute.Constructor qualified
import Test.Kore.Attribute.Function qualified
import Test.Kore.Attribute.Functional qualified
import Test.Kore.Attribute.Hook qualified
import Test.Kore.Attribute.Idem qualified
import Test.Kore.Attribute.Injective qualified
import Test.Kore.Attribute.Label qualified
import Test.Kore.Attribute.NonExecutable qualified
import Test.Kore.Attribute.Overload qualified
import Test.Kore.Attribute.Owise qualified
import Test.Kore.Attribute.Pattern.ConstructorLike qualified
import Test.Kore.Attribute.Pattern.Defined qualified
import Test.Kore.Attribute.Pattern.FreeVariables qualified
import Test.Kore.Attribute.Pattern.Function qualified
import Test.Kore.Attribute.Pattern.Functional qualified
import Test.Kore.Attribute.Pattern.Sort qualified
import Test.Kore.Attribute.Priority qualified
import Test.Kore.Attribute.ProductionID qualified
import Test.Kore.Attribute.Simplification qualified
import Test.Kore.Attribute.Smtlib qualified
import Test.Kore.Attribute.Sort.ConstructorsBuilder qualified
import Test.Kore.Attribute.Sort.HasDomainValues qualified
import Test.Kore.Attribute.Sort.Unit qualified
import Test.Kore.Attribute.SortInjection qualified
import Test.Kore.Attribute.Subsort qualified
import Test.Kore.Attribute.Symbol qualified
import Test.Kore.Attribute.Symbol.Anywhere qualified
import Test.Kore.Attribute.Symbol.Klabel qualified
import Test.Kore.Attribute.Symbol.Memo qualified
import Test.Kore.Attribute.Symbol.NoEvaluators qualified
import Test.Kore.Attribute.Symbol.SymbolKywd qualified
import Test.Kore.Attribute.Trusted qualified
import Test.Kore.Attribute.UniqueId qualified
import Test.Kore.BugReport qualified
import Test.Kore.Builtin qualified
import Test.Kore.Builtin.AssocComm.CeilSimplifier qualified
import Test.Kore.Builtin.Bool qualified
import Test.Kore.Builtin.Encoding qualified
import Test.Kore.Builtin.Endianness qualified
import Test.Kore.Builtin.Inj qualified
import Test.Kore.Builtin.Int qualified
import Test.Kore.Builtin.InternalBytes qualified
import Test.Kore.Builtin.KEqual qualified
import Test.Kore.Builtin.Krypto qualified
import Test.Kore.Builtin.List qualified
import Test.Kore.Builtin.Map qualified
import Test.Kore.Builtin.Set qualified
import Test.Kore.Builtin.Signedness qualified
import Test.Kore.Builtin.String qualified
import Test.Kore.Equation.Application qualified
import Test.Kore.Equation.Sentence qualified
import Test.Kore.Equation.Simplification qualified
import Test.Kore.Error qualified
import Test.Kore.Exec qualified
import Test.Kore.IndexedModule.Error qualified
import Test.Kore.IndexedModule.OverloadGraph qualified
import Test.Kore.IndexedModule.Resolvers qualified
import Test.Kore.IndexedModule.SortGraph qualified
import Test.Kore.Internal.ApplicationSorts qualified
import Test.Kore.Internal.From qualified
import Test.Kore.Internal.Key qualified
import Test.Kore.Internal.MultiAnd qualified
import Test.Kore.Internal.MultiExists qualified
import Test.Kore.Internal.OrPattern qualified
import Test.Kore.Internal.Pattern qualified
import Test.Kore.Internal.Predicate qualified
import Test.Kore.Internal.SideCondition qualified
import Test.Kore.Internal.Substitution qualified
import Test.Kore.Internal.TermLike qualified
import Test.Kore.Log.DebugEvaluateCondition qualified
import Test.Kore.Log.ErrorBottomTotalFunction qualified
import Test.Kore.Log.WarnFunctionWithoutEvaluators qualified
import Test.Kore.Log.WarnSymbolSMTRepresentation qualified
import Test.Kore.Options qualified
import Test.Kore.Parser.Lexer qualified
import Test.Kore.Parser.Parser qualified
import Test.Kore.Reachability.Claim qualified
import Test.Kore.Reachability.MockAllPath qualified
import Test.Kore.Reachability.OnePathStrategy qualified
import Test.Kore.Reachability.Prove qualified
import Test.Kore.Reachability.SomeClaim qualified
import Test.Kore.Repl.Graph qualified
import Test.Kore.Repl.Interpreter qualified
import Test.Kore.Repl.Parser qualified
import Test.Kore.Rewrite qualified
import Test.Kore.Rewrite.AntiLeft qualified
import Test.Kore.Rewrite.Axiom.EvaluationStrategy qualified
import Test.Kore.Rewrite.Axiom.Identifier qualified
import Test.Kore.Rewrite.Axiom.Matcher qualified
import Test.Kore.Rewrite.Axiom.Registry qualified
import Test.Kore.Rewrite.ClaimPattern qualified
import Test.Kore.Rewrite.Function.Evaluator qualified
import Test.Kore.Rewrite.Function.Integration qualified
import Test.Kore.Rewrite.Function.Memo qualified
import Test.Kore.Rewrite.Implication qualified
import Test.Kore.Rewrite.MockSymbols qualified
import Test.Kore.Rewrite.Remainder qualified
import Test.Kore.Rewrite.RewriteStep qualified
import Test.Kore.Rewrite.RewritingVariable qualified
import Test.Kore.Rewrite.Rule qualified
import Test.Kore.Rewrite.Rule.Expand qualified
import Test.Kore.Rewrite.Rule.Simplify qualified
import Test.Kore.Rewrite.RulePattern qualified
import Test.Kore.Rewrite.SMT.Evaluator qualified
import Test.Kore.Rewrite.SMT.Representation.All qualified
import Test.Kore.Rewrite.SMT.Representation.Sorts qualified
import Test.Kore.Rewrite.SMT.Representation.Symbols qualified
import Test.Kore.Rewrite.SMT.Sorts qualified
import Test.Kore.Rewrite.SMT.Symbols qualified
import Test.Kore.Rewrite.SMT.Translate qualified
import Test.Kore.Rewrite.Strategy qualified
import Test.Kore.Rewrite.Transition qualified
import Test.Kore.Simplify.And qualified
import Test.Kore.Simplify.AndTerms qualified
import Test.Kore.Simplify.Application qualified
import Test.Kore.Simplify.Bottom qualified
import Test.Kore.Simplify.Ceil qualified
import Test.Kore.Simplify.Condition qualified
import Test.Kore.Simplify.DomainValue qualified
import Test.Kore.Simplify.Equals qualified
import Test.Kore.Simplify.Exists qualified
import Test.Kore.Simplify.Floor qualified
import Test.Kore.Simplify.Forall qualified
import Test.Kore.Simplify.Iff qualified
import Test.Kore.Simplify.Implies qualified
import Test.Kore.Simplify.Inj qualified
import Test.Kore.Simplify.InjSimplifier qualified
import Test.Kore.Simplify.Integration qualified
import Test.Kore.Simplify.IntegrationProperty qualified
import Test.Kore.Simplify.InternalList qualified
import Test.Kore.Simplify.InternalMap qualified
import Test.Kore.Simplify.InternalSet qualified
import Test.Kore.Simplify.Next qualified
import Test.Kore.Simplify.Not qualified
import Test.Kore.Simplify.Or qualified
import Test.Kore.Simplify.OrPattern qualified
import Test.Kore.Simplify.Overloading qualified
import Test.Kore.Simplify.Pattern qualified
import Test.Kore.Simplify.Predicate qualified
import Test.Kore.Simplify.StringLiteral qualified
import Test.Kore.Simplify.SubstitutionSimplifier qualified
import Test.Kore.Simplify.TermLike qualified
import Test.Kore.Simplify.Top qualified
import Test.Kore.Syntax.Id qualified
import Test.Kore.Syntax.Json qualified
import Test.Kore.Syntax.Json.Roundtrips qualified
import Test.Kore.Syntax.Variable qualified
import Test.Kore.TopBottom qualified
import Test.Kore.Unification.SubstitutionNormalization qualified
import Test.Kore.Unification.Unifier qualified
import Test.Kore.Unification.UnifierT qualified
import Test.Kore.Unparser qualified
import Test.Kore.Validate.DefinitionVerifier.Imports qualified
import Test.Kore.Validate.DefinitionVerifier.PatternVerifier qualified
import Test.Kore.Validate.DefinitionVerifier.SentenceVerifier qualified
import Test.Kore.Validate.DefinitionVerifier.SortUsage qualified
import Test.Kore.Validate.DefinitionVerifier.UniqueNames qualified
import Test.Kore.Validate.DefinitionVerifier.UniqueSortVariables qualified
import Test.Kore.Variables.Fresh qualified
import Test.Kore.Variables.Target qualified
import Test.Pretty qualified
import Test.SMT.AST qualified
import Test.SQL qualified
import Test.Stats qualified
import Test.Tasty qualified as T
import Test.Tasty.Hedgehog qualified as H
import Test.Tasty.Ingredients qualified as T
import Test.Tasty.QuickCheck qualified as QC
import Test.Tasty.Runners qualified
import Test.Tasty.Runners.Reporter qualified
import Prelude

class TestGroup a where testGroup :: String -> a -> IO T.TestTree
instance TestGroup T.TestTree where testGroup _ a = pure a
instance TestGroup [T.TestTree] where testGroup n a = pure $ T.testGroup n a
instance TestGroup (IO T.TestTree) where testGroup _ a = a
instance TestGroup (IO [T.TestTree]) where testGroup n a = T.testGroup n <$> a

tests :: IO T.TestTree
tests = do
    t0 <- testGroup "layoutOneLine" Test.Pretty.test_layoutOneLine

    t1 <- pure $ H.testProperty "Injection Maybe" Test.Injection.hprop_Injection_Maybe

    t2 <- pure $ H.testProperty "Injection Dynamic" Test.Injection.hprop_Injection_Dynamic

    t3 <- testGroup "Unit" Test.SQL.test_Unit

    t4 <- testGroup "Either" Test.SQL.test_Either

    t5 <- testGroup "Maybe" Test.SQL.test_Maybe

    t6 <- testGroup "List" Test.SQL.test_List

    t7 <- testGroup "NonEmpty" Test.SQL.test_NonEmpty

    t8 <- testGroup "debug" Test.Debug.test_debug

    t9 <- testGroup "debugPrec" Test.Debug.test_debugPrec

    t10 <- testGroup "Debug" Test.Debug.test_Debug

    t11 <- testGroup "diff" Test.Debug.test_diff

    t12 <- testGroup "Stats" Test.Stats.test_Stats

    t13 <- pure $ H.testProperty "transitiveOrd" Test.Data.Sup.hprop_transitiveOrd

    t14 <- pure $ H.testProperty "reflexiveOrd" Test.Data.Sup.hprop_reflexiveOrd

    t15 <- pure $ H.testProperty "antisymmetricOrd" Test.Data.Sup.hprop_antisymmetricOrd

    t16 <- pure $ H.testProperty "reflexiveEq" Test.Data.Sup.hprop_reflexiveEq

    t17 <- pure $ H.testProperty "symmetricEq" Test.Data.Sup.hprop_symmetricEq

    t18 <- pure $ H.testProperty "transitiveEq" Test.Data.Sup.hprop_transitiveEq

    t19 <- pure $ H.testProperty "negativeEq" Test.Data.Sup.hprop_negativeEq

    t20 <- pure $ H.testProperty "associativeSemigroup" Test.Data.Sup.hprop_associativeSemigroup

    t21 <- pure $ H.testProperty "commutativeSemigroup" Test.Data.Sup.hprop_commutativeSemigroup

    t22 <- pure $ H.testProperty "idempotentSemigroup" Test.Data.Sup.hprop_idempotentSemigroup

    t23 <- pure $ H.testProperty "identityFunctor" Test.Data.Sup.hprop_identityFunctor

    t24 <- pure $ H.testProperty "compositionFunctor" Test.Data.Sup.hprop_compositionFunctor

    t25 <- pure $ H.testProperty "identityApplicative" Test.Data.Sup.hprop_identityApplicative

    t26 <- pure $ H.testProperty "compositionApplicative" Test.Data.Sup.hprop_compositionApplicative

    t27 <- pure $ H.testProperty "homomorphismApplicative" Test.Data.Sup.hprop_homomorphismApplicative

    t28 <- pure $ H.testProperty "interchangeApplicative" Test.Data.Sup.hprop_interchangeApplicative

    t29 <- pure $ QC.testProperty "append" Test.Data.Limit.prop_append

    t30 <- pure $ QC.testProperty "dominate" Test.Data.Limit.prop_dominate

    t31 <- pure $ QC.testProperty "homomorphism" Test.Data.Limit.prop_homomorphism

    t32 <- pure $ QC.testProperty "identity" Test.Data.Limit.prop_identity

    t33 <- pure $ H.testProperty "hashes id" Test.Data.InternedText.hprop_hashes_id

    t34 <- pure $ H.testProperty "tests equality using id" Test.Data.InternedText.hprop_tests_equality_using_id

    t35 <- pure $ H.testProperty "internText does not change the strings contents" Test.Data.InternedText.hprop_internText_does_not_change_the_strings_contents

    t36 <- pure $ H.testProperty "internText returns the same id for the same string" Test.Data.InternedText.hprop_internText_returns_the_same_id_for_the_same_string

    t37 <- pure $ H.testProperty "internText returns different ids for different strings" Test.Data.InternedText.hprop_internText_returns_different_ids_for_different_strings

    t38 <- testGroup "topologicalSort" Test.Data.Graph.TopologicalSort.test_topologicalSort

    t39 <- testGroup "TermLike" Test.Kore.TopBottom.test_TermLike

    t40 <- testGroup "Predicate" Test.Kore.TopBottom.test_Predicate

    t41 <- testGroup "exec" Test.Kore.Exec.test_exec

    t42 <- testGroup "execPriority" Test.Kore.Exec.test_execPriority

    t43 <- testGroup "execBottom" Test.Kore.Exec.test_execBottom

    t44 <- testGroup "execBranch" Test.Kore.Exec.test_execBranch

    t45 <- testGroup "execBranch1Stuck" Test.Kore.Exec.test_execBranch1Stuck

    t46 <- testGroup "execDepthInfo" Test.Kore.Exec.test_execDepthInfo

    t47 <- testGroup "searchPriority" Test.Kore.Exec.test_searchPriority

    t48 <- testGroup "searchExceedingBreadthLimit" Test.Kore.Exec.test_searchExceedingBreadthLimit

    t49 <- testGroup "execGetExitCode" Test.Kore.Exec.test_execGetExitCode

    t50 <- testGroup "execDepthLimitExceeded" Test.Kore.Exec.test_execDepthLimitExceeded

    t51 <- testGroup "matchDisjunction" Test.Kore.Exec.test_matchDisjunction

    t52 <- testGroup "checkFunctions" Test.Kore.Exec.test_checkFunctions

    t53 <- testGroup "simplify" Test.Kore.Exec.test_simplify

    t54 <- testGroup "rpcExecDepth" Test.Kore.Exec.test_rpcExecDepth

    t55 <- testGroup "internalize" Test.Kore.Builtin.test_internalize

    t56 <- testGroup "sortModuleClaims" Test.Kore.Builtin.test_sortModuleClaims

    t57 <- testGroup "flags" Test.Kore.Options.test_flags

    t58 <- testGroup "options" Test.Kore.Options.test_options

    t59 <- testGroup "assertRight" Test.Kore.Error.test_assertRight

    t60 <- testGroup "Parse BugReportOption" Test.Kore.BugReport.test_Parse_BugReportOption

    t61 <- testGroup "parse" Test.Kore.BugReport.test_parse

    t62 <- testGroup "parse" Test.Kore.Unparser.test_parse

    t63 <- testGroup "unparse" Test.Kore.Unparser.test_unparse

    t64 <- testGroup "unparseGeneric" Test.Kore.Unparser.test_unparseGeneric

    t65 <- testGroup "stepStrategy" Test.Kore.Rewrite.test_stepStrategy

    t66 <- testGroup "executionStrategy" Test.Kore.Rewrite.test_executionStrategy

    t67 <- testGroup "simplifyEquation" Test.Kore.Equation.Simplification.test_simplifyEquation

    t68 <- testGroup "fromSentenceAxiom" Test.Kore.Equation.Sentence.test_fromSentenceAxiom

    t69 <- testGroup "attemptEquation" Test.Kore.Equation.Application.test_attemptEquation

    t70 <- testGroup "applySubstitutionAndSimplify" Test.Kore.Equation.Application.test_applySubstitutionAndSimplify

    t71 <- testGroup "uniqueSortVariables" Test.Kore.Validate.DefinitionVerifier.UniqueSortVariables.test_uniqueSortVariables

    t72 <- testGroup "FreeVarInRHS" Test.Kore.Validate.DefinitionVerifier.SentenceVerifier.test_FreeVarInRHS

    t73 <- testGroup "uniqueNames" Test.Kore.Validate.DefinitionVerifier.UniqueNames.test_uniqueNames

    t74 <- testGroup "sortUsage" Test.Kore.Validate.DefinitionVerifier.SortUsage.test_sortUsage

    t75 <- testGroup "imports" Test.Kore.Validate.DefinitionVerifier.Imports.test_imports

    t76 <- testGroup "patternVerifier" Test.Kore.Validate.DefinitionVerifier.PatternVerifier.test_patternVerifier

    t77 <- testGroup "verifyBinder" Test.Kore.Validate.DefinitionVerifier.PatternVerifier.test_verifyBinder

    t78 <- testGroup "instance Table ErrorBottomTotalFunction" Test.Kore.Log.ErrorBottomTotalFunction.test_instance_Table_ErrorBottomTotalFunction

    t79 <- testGroup "instance Table DebugEvaluateCondition" Test.Kore.Log.DebugEvaluateCondition.test_instance_Table_DebugEvaluateCondition

    t80 <- testGroup "instance Table WarnFunctionWithoutEvaluators" Test.Kore.Log.WarnFunctionWithoutEvaluators.test_instance_Table_WarnFunctionWithoutEvaluators

    t81 <- testGroup "instance Table WarnSymbolSMTRepresentation" Test.Kore.Log.WarnSymbolSMTRepresentation.test_instance_Table_WarnSymbolSMTRepresentation

    t82 <- testGroup "id" Test.Kore.AST.Common.test_id

    t83 <- testGroup "prettyPrintAstLocation" Test.Kore.AST.Common.test_prettyPrintAstLocation

    t84 <- testGroup "replInterpreter" Test.Kore.Repl.Interpreter.test_replInterpreter

    t85 <- testGroup "replParser" Test.Kore.Repl.Parser.test_replParser

    t86 <- testGroup "graph" Test.Kore.Repl.Graph.test_graph

    t87 <- testGroup "checkImplication" Test.Kore.Reachability.Claim.test_checkImplication

    t88 <- testGroup "checkSimpleImplication" Test.Kore.Reachability.Claim.test_checkSimpleImplication

    t89 <- testGroup "simplifyRightHandSide" Test.Kore.Reachability.Claim.test_simplifyRightHandSide

    t90 <- testGroup "proveClaims" Test.Kore.Reachability.Prove.test_proveClaims

    t91 <- testGroup "transitionRule" Test.Kore.Reachability.Prove.test_transitionRule

    t92 <- testGroup "extractClaim" Test.Kore.Reachability.SomeClaim.test_extractClaim

    t93 <- testGroup "onePathStrategy" Test.Kore.Reachability.OnePathStrategy.test_onePathStrategy

    t94 <- testGroup "unprovenNodes" Test.Kore.Reachability.MockAllPath.test_unprovenNodes

    t95 <- testGroup "transitionRule Begin" Test.Kore.Reachability.MockAllPath.test_transitionRule_Begin

    t96 <- testGroup "transitionRule CheckImplication" Test.Kore.Reachability.MockAllPath.test_transitionRule_CheckImplication

    t97 <- testGroup "transitionRule ApplyClaims" Test.Kore.Reachability.MockAllPath.test_transitionRule_ApplyClaims

    t98 <- testGroup "transitionRule ApplyAxioms" Test.Kore.Reachability.MockAllPath.test_transitionRule_ApplyAxioms

    t99 <- testGroup "runStrategy" Test.Kore.Reachability.MockAllPath.test_runStrategy

    t100 <- testGroup "checkImplication" Test.Kore.Reachability.Claim.test_checkImplication

    t101 <- testGroup "checkSimpleImplication" Test.Kore.Reachability.Claim.test_checkSimpleImplication

    t102 <- testGroup "simplifyRightHandSide" Test.Kore.Reachability.Claim.test_simplifyRightHandSide

    t103 <- testGroup "axiomPatterns" Test.Kore.Rewrite.Rule.test_axiomPatterns

    t104 <- testGroup "patternToAxiomPatternAndBack" Test.Kore.Rewrite.Rule.test_patternToAxiomPatternAndBack

    t105 <- testGroup "rewritePatternToRewriteRuleAndBack" Test.Kore.Rewrite.Rule.test_rewritePatternToRewriteRuleAndBack

    t106 <- testGroup "builtinMap" Test.Kore.Rewrite.MockSymbols.test_builtinMap

    t107 <- testGroup "builtinSet" Test.Kore.Rewrite.MockSymbols.test_builtinSet

    t108 <- testGroup "applyInitialConditions" Test.Kore.Rewrite.RewriteStep.test_applyInitialConditions

    t109 <- testGroup "renameRuleVariables" Test.Kore.Rewrite.RewriteStep.test_renameRuleVariables

    t110 <- testGroup "unifyRule" Test.Kore.Rewrite.RewriteStep.test_unifyRule

    t111 <- testGroup "applyRewriteRule " Test.Kore.Rewrite.RewriteStep.test_applyRewriteRule_

    t112 <- testGroup "applyRewriteRulesParallel" Test.Kore.Rewrite.RewriteStep.test_applyRewriteRulesParallel

    t113 <- testGroup "applyRewriteRulesSequence" Test.Kore.Rewrite.RewriteStep.test_applyRewriteRulesSequence

    t114 <- testGroup "narrowing" Test.Kore.Rewrite.RewriteStep.test_narrowing

    t115 <- pure $ QC.testProperty "SeqContinueIdentity" Test.Kore.Rewrite.Strategy.prop_SeqContinueIdentity

    t116 <- pure $ QC.testProperty "Continue" Test.Kore.Rewrite.Strategy.prop_Continue

    t117 <- pure $ QC.testProperty "depthLimit" Test.Kore.Rewrite.Strategy.prop_depthLimit

    t118 <- pure $ QC.testProperty "pickLongest" Test.Kore.Rewrite.Strategy.prop_pickLongest

    t119 <- pure $ QC.testProperty "pickFinal" Test.Kore.Rewrite.Strategy.prop_pickFinal

    t120 <- pure $ QC.testProperty "pickOne" Test.Kore.Rewrite.Strategy.prop_pickOne

    t121 <- pure $ QC.testProperty "pickStar" Test.Kore.Rewrite.Strategy.prop_pickStar

    t122 <- pure $ QC.testProperty "pickPlus" Test.Kore.Rewrite.Strategy.prop_pickPlus

    t123 <- testGroup "existentiallyQuantifyTarget" Test.Kore.Rewrite.Remainder.test_existentiallyQuantifyTarget

    t124 <- testGroup "FreshPartialOrd RewritingVariableName" Test.Kore.Rewrite.RewritingVariable.test_FreshPartialOrd_RewritingVariableName

    t125 <- testGroup "FreshPartialOrd SomeVariableName RewritingVariableName" Test.Kore.Rewrite.RewritingVariable.test_FreshPartialOrd_SomeVariableName_RewritingVariableName

    t126 <- testGroup "antiLeft" Test.Kore.Rewrite.AntiLeft.test_antiLeft

    t127 <- testGroup "freeVariables" Test.Kore.Rewrite.RulePattern.test_freeVariables

    t128 <- testGroup "refreshRule" Test.Kore.Rewrite.RulePattern.test_refreshRule

    t129 <- testGroup "ifte" Test.Kore.Rewrite.Transition.test_ifte

    t130 <- testGroup "record" Test.Kore.Rewrite.Transition.test_record

    t131 <- testGroup "freeVariables" Test.Kore.Rewrite.ClaimPattern.test_freeVariables

    t132 <- testGroup "refreshRule" Test.Kore.Rewrite.ClaimPattern.test_refreshRule

    t133 <- testGroup "freeVariables" Test.Kore.Rewrite.Implication.test_freeVariables

    t134 <- testGroup "refreshRule" Test.Kore.Rewrite.Implication.test_refreshRule

    t135 <- testGroup "substitute" Test.Kore.Rewrite.Implication.test_substitute

    t136 <- testGroup "simplifyRule OnePathClaim" Test.Kore.Rewrite.Rule.Simplify.test_simplifyRule_OnePathClaim

    t137 <- testGroup "simplifyClaimRule" Test.Kore.Rewrite.Rule.Simplify.test_simplifyClaimRule

    t138 <- testGroup "expandRule" Test.Kore.Rewrite.Rule.Expand.test_expandRule

    t139 <- testGroup "functionIntegration" Test.Kore.Rewrite.Function.Integration.test_functionIntegration

    t140 <- testGroup "Nat" Test.Kore.Rewrite.Function.Integration.test_Nat

    t141 <- testGroup "short circuit" Test.Kore.Rewrite.Function.Integration.test_short_circuit

    t142 <- testGroup "List" Test.Kore.Rewrite.Function.Integration.test_List

    t143 <- testGroup "lookupMap" Test.Kore.Rewrite.Function.Integration.test_lookupMap

    t144 <- testGroup "updateMap" Test.Kore.Rewrite.Function.Integration.test_updateMap

    t145 <- testGroup "updateList" Test.Kore.Rewrite.Function.Integration.test_updateList

    t146 <- testGroup "Ceil" Test.Kore.Rewrite.Function.Integration.test_Ceil

    t147 <- testGroup "evaluateApplication" Test.Kore.Rewrite.Function.Evaluator.test_evaluateApplication

    t148 <- testGroup "Self" Test.Kore.Rewrite.Function.Memo.test_Self

    t149 <- testGroup "matcherEqualHeads" Test.Kore.Rewrite.Axiom.Matcher.test_matcherEqualHeads

    t150 <- testGroup "matcherVariableFunction" Test.Kore.Rewrite.Axiom.Matcher.test_matcherVariableFunction

    t151 <- testGroup "matcherNonVarToPattern" Test.Kore.Rewrite.Axiom.Matcher.test_matcherNonVarToPattern

    t152 <- testGroup "matcherMergeSubresults" Test.Kore.Rewrite.Axiom.Matcher.test_matcherMergeSubresults

    t153 <- testGroup "matching Bool" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Bool

    t154 <- testGroup "matching Int" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Int

    t155 <- testGroup "matching String" Test.Kore.Rewrite.Axiom.Matcher.test_matching_String

    t156 <- testGroup "matching List" Test.Kore.Rewrite.Axiom.Matcher.test_matching_List

    t157 <- testGroup "matching Set" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Set

    t158 <- testGroup "matching Map" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Map

    t159 <- testGroup "matching Pair" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Pair

    t160 <- testGroup "matching Exists" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Exists

    t161 <- testGroup "matching Forall" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Forall

    t162 <- testGroup "matching Equals" Test.Kore.Rewrite.Axiom.Matcher.test_matching_Equals

    t163 <- testGroup "matching And" Test.Kore.Rewrite.Axiom.Matcher.test_matching_And

    t164 <- testGroup "matcherOverloading" Test.Kore.Rewrite.Axiom.Matcher.test_matcherOverloading

    t165 <- testGroup "functionRegistry" Test.Kore.Rewrite.Axiom.Registry.test_functionRegistry

    t166 <- testGroup "definitionEvaluation" Test.Kore.Rewrite.Axiom.EvaluationStrategy.test_definitionEvaluation

    t167 <- testGroup "firstFullEvaluation" Test.Kore.Rewrite.Axiom.EvaluationStrategy.test_firstFullEvaluation

    t168 <- testGroup "simplifierWithFallback" Test.Kore.Rewrite.Axiom.EvaluationStrategy.test_simplifierWithFallback

    t169 <- testGroup "builtinEvaluation" Test.Kore.Rewrite.Axiom.EvaluationStrategy.test_builtinEvaluation

    t170 <- testGroup "attemptEquations" Test.Kore.Rewrite.Axiom.EvaluationStrategy.test_attemptEquations

    t171 <- testGroup "matchAxiomIdentifier" Test.Kore.Rewrite.Axiom.Identifier.test_matchAxiomIdentifier

    t172 <- testGroup "translatePredicateWith" Test.Kore.Rewrite.SMT.Translate.test_translatePredicateWith

    t173 <- testGroup "sortDeclaration" Test.Kore.Rewrite.SMT.Symbols.test_sortDeclaration

    t174 <- testGroup "resolve" Test.Kore.Rewrite.SMT.Symbols.test_resolve

    t175 <- testGroup "evaluableSyntaxPredicate" Test.Kore.Rewrite.SMT.Evaluator.test_evaluableSyntaxPredicate

    t176 <- testGroup "evaluableConditional" Test.Kore.Rewrite.SMT.Evaluator.test_evaluableConditional

    t177 <- testGroup "evaluableMultiOr" Test.Kore.Rewrite.SMT.Evaluator.test_evaluableMultiOr

    t178 <- testGroup "andNegation" Test.Kore.Rewrite.SMT.Evaluator.test_andNegation

    t179 <- testGroup "Int contradictions" Test.Kore.Rewrite.SMT.Evaluator.test_Int_contradictions

    t180 <- testGroup "Bool contradictions" Test.Kore.Rewrite.SMT.Evaluator.test_Bool_contradictions

    t181 <- testGroup "sortDeclaration" Test.Kore.Rewrite.SMT.Sorts.test_sortDeclaration

    t182 <- testGroup "symbolParsing" Test.Kore.Rewrite.SMT.Representation.Symbols.test_symbolParsing

    t183 <- testGroup "symbolParsing" Test.Kore.Rewrite.SMT.Representation.All.test_symbolParsing

    t184 <- testGroup "sortParsing" Test.Kore.Rewrite.SMT.Representation.Sorts.test_sortParsing

    t185 <- testGroup "or" Test.Kore.Builtin.Bool.test_or

    t186 <- testGroup "orElse" Test.Kore.Builtin.Bool.test_orElse

    t187 <- testGroup "and" Test.Kore.Builtin.Bool.test_and

    t188 <- testGroup "andThen" Test.Kore.Builtin.Bool.test_andThen

    t189 <- testGroup "xor" Test.Kore.Builtin.Bool.test_xor

    t190 <- testGroup "ne" Test.Kore.Builtin.Bool.test_ne

    t191 <- testGroup "eq" Test.Kore.Builtin.Bool.test_eq

    t192 <- testGroup "not" Test.Kore.Builtin.Bool.test_not

    t193 <- testGroup "implies" Test.Kore.Builtin.Bool.test_implies

    t194 <- pure $ H.testProperty "unparse" Test.Kore.Builtin.Bool.hprop_unparse

    t195 <- testGroup "unifyBoolValues" Test.Kore.Builtin.Bool.test_unifyBoolValues

    t196 <- testGroup "unifyBoolAnd" Test.Kore.Builtin.Bool.test_unifyBoolAnd

    t197 <- testGroup "unifyBoolOr" Test.Kore.Builtin.Bool.test_unifyBoolOr

    t198 <- testGroup "contradiction" Test.Kore.Builtin.Bool.test_contradiction

    t199 <- testGroup "verify" Test.Kore.Builtin.Signedness.test_verify

    t200 <- testGroup "match" Test.Kore.Builtin.Signedness.test_match

    t201 <- testGroup "unify" Test.Kore.Builtin.Signedness.test_unify

    t202 <- testGroup "ecdsaRecover" Test.Kore.Builtin.Krypto.test_ecdsaRecover

    t203 <- testGroup "secp256k1EcdsaRecover" Test.Kore.Builtin.Krypto.test_secp256k1EcdsaRecover

    t204 <- testGroup "keccak256" Test.Kore.Builtin.Krypto.test_keccak256

    t205 <- testGroup "hashKeccak256" Test.Kore.Builtin.Krypto.test_hashKeccak256

    t206 <- testGroup "sha256" Test.Kore.Builtin.Krypto.test_sha256

    t207 <- testGroup "hashSha256" Test.Kore.Builtin.Krypto.test_hashSha256

    t208 <- testGroup "sha3256" Test.Kore.Builtin.Krypto.test_sha3256

    t209 <- testGroup "hashSha3 256" Test.Kore.Builtin.Krypto.test_hashSha3_256

    t210 <- testGroup "ripemd160" Test.Kore.Builtin.Krypto.test_ripemd160

    t211 <- testGroup "hashRipemd160" Test.Kore.Builtin.Krypto.test_hashRipemd160

    t212 <- testGroup "update" Test.Kore.Builtin.InternalBytes.test_update

    t213 <- testGroup "get" Test.Kore.Builtin.InternalBytes.test_get

    t214 <- testGroup "substr" Test.Kore.Builtin.InternalBytes.test_substr

    t215 <- testGroup "replaceAt" Test.Kore.Builtin.InternalBytes.test_replaceAt

    t216 <- testGroup "padRight" Test.Kore.Builtin.InternalBytes.test_padRight

    t217 <- testGroup "padLeft" Test.Kore.Builtin.InternalBytes.test_padLeft

    t218 <- testGroup "reverse" Test.Kore.Builtin.InternalBytes.test_reverse

    t219 <- testGroup "length" Test.Kore.Builtin.InternalBytes.test_length

    t220 <- testGroup "concat" Test.Kore.Builtin.InternalBytes.test_concat

    t221 <- testGroup "reverse length" Test.Kore.Builtin.InternalBytes.test_reverse_length

    t222 <- testGroup "update get" Test.Kore.Builtin.InternalBytes.test_update_get

    t223 <- testGroup "bytes2string string2bytes" Test.Kore.Builtin.InternalBytes.test_bytes2string_string2bytes

    t224 <- testGroup "decodeBytes encodeBytes" Test.Kore.Builtin.InternalBytes.test_decodeBytes_encodeBytes

    t225 <- testGroup "decodeBytes" Test.Kore.Builtin.InternalBytes.test_decodeBytes

    t226 <- testGroup "encodeBytes" Test.Kore.Builtin.InternalBytes.test_encodeBytes

    t227 <- testGroup "int2bytes" Test.Kore.Builtin.InternalBytes.test_int2bytes

    t228 <- testGroup "bytes2int" Test.Kore.Builtin.InternalBytes.test_bytes2int

    t229 <- testGroup "InternalBytes" Test.Kore.Builtin.InternalBytes.test_InternalBytes

    t230 <- testGroup "unparse" Test.Kore.Builtin.InternalBytes.test_unparse

    t231 <- testGroup "patternVerifierHook" Test.Kore.Builtin.Inj.test_patternVerifierHook

    t232 <- testGroup "eq" Test.Kore.Builtin.String.test_eq

    t233 <- testGroup "lt" Test.Kore.Builtin.String.test_lt

    t234 <- testGroup "concat" Test.Kore.Builtin.String.test_concat

    t235 <- testGroup "substr" Test.Kore.Builtin.String.test_substr

    t236 <- testGroup "length" Test.Kore.Builtin.String.test_length

    t237 <- testGroup "chr" Test.Kore.Builtin.String.test_chr

    t238 <- testGroup "ord" Test.Kore.Builtin.String.test_ord

    t239 <- testGroup "find" Test.Kore.Builtin.String.test_find

    t240 <- testGroup "string2Base" Test.Kore.Builtin.String.test_string2Base

    t241 <- testGroup "base2String" Test.Kore.Builtin.String.test_base2String

    t242 <- testGroup "string2Int" Test.Kore.Builtin.String.test_string2Int

    t243 <- testGroup "int2String" Test.Kore.Builtin.String.test_int2String

    t244 <- testGroup "token2String" Test.Kore.Builtin.String.test_token2String

    t245 <- testGroup "string2Token" Test.Kore.Builtin.String.test_string2Token

    t246 <- testGroup "unifyStringEq" Test.Kore.Builtin.String.test_unifyStringEq

    t247 <- testGroup "contradiction" Test.Kore.Builtin.String.test_contradiction

    t248 <- testGroup "decodeEncode" Test.Kore.Builtin.Encoding.test_decodeEncode

    t249 <- testGroup "parseBase16" Test.Kore.Builtin.Encoding.test_parseBase16

    t250 <- testGroup "lookupUnit" Test.Kore.Builtin.Map.test_lookupUnit

    t251 <- testGroup "lookupUpdate" Test.Kore.Builtin.Map.test_lookupUpdate

    t252 <- testGroup "removeUnit" Test.Kore.Builtin.Map.test_removeUnit

    t253 <- testGroup "sizeUnit" Test.Kore.Builtin.Map.test_sizeUnit

    t254 <- testGroup "removeKeyNotIn" Test.Kore.Builtin.Map.test_removeKeyNotIn

    t255 <- testGroup "removeKeyIn" Test.Kore.Builtin.Map.test_removeKeyIn

    t256 <- testGroup "removeAllMapUnit" Test.Kore.Builtin.Map.test_removeAllMapUnit

    t257 <- testGroup "removeAllSetUnit" Test.Kore.Builtin.Map.test_removeAllSetUnit

    t258 <- testGroup "removeAll" Test.Kore.Builtin.Map.test_removeAll

    t259 <- testGroup "concatUnit" Test.Kore.Builtin.Map.test_concatUnit

    t260 <- testGroup "lookupConcatUniqueKeys" Test.Kore.Builtin.Map.test_lookupConcatUniqueKeys

    t261 <- testGroup "concatDuplicateKeys" Test.Kore.Builtin.Map.test_concatDuplicateKeys

    t262 <- testGroup "concatCommutes" Test.Kore.Builtin.Map.test_concatCommutes

    t263 <- testGroup "concatAssociates" Test.Kore.Builtin.Map.test_concatAssociates

    t264 <- testGroup "inKeysUnit" Test.Kore.Builtin.Map.test_inKeysUnit

    t265 <- testGroup "keysUnit" Test.Kore.Builtin.Map.test_keysUnit

    t266 <- testGroup "keysElement" Test.Kore.Builtin.Map.test_keysElement

    t267 <- testGroup "keys" Test.Kore.Builtin.Map.test_keys

    t268 <- testGroup "keysListUnit" Test.Kore.Builtin.Map.test_keysListUnit

    t269 <- testGroup "keysListElement" Test.Kore.Builtin.Map.test_keysListElement

    t270 <- testGroup "keysList" Test.Kore.Builtin.Map.test_keysList

    t271 <- testGroup "inKeysElement" Test.Kore.Builtin.Map.test_inKeysElement

    t272 <- testGroup "values" Test.Kore.Builtin.Map.test_values

    t273 <- testGroup "inclusion" Test.Kore.Builtin.Map.test_inclusion

    t274 <- testGroup "simplify" Test.Kore.Builtin.Map.test_simplify

    t275 <- testGroup "symbolic" Test.Kore.Builtin.Map.test_symbolic

    t276 <- testGroup "isBuiltin" Test.Kore.Builtin.Map.test_isBuiltin

    t277 <- testGroup "unifyConcrete" Test.Kore.Builtin.Map.test_unifyConcrete

    t278 <- testGroup "unifyEmptyWithEmpty" Test.Kore.Builtin.Map.test_unifyEmptyWithEmpty

    t279 <- testGroup "unifySelectFromEmpty" Test.Kore.Builtin.Map.test_unifySelectFromEmpty

    t280 <- testGroup "unifySelectFromSingleton" Test.Kore.Builtin.Map.test_unifySelectFromSingleton

    t281 <- testGroup "unifySelectSingletonFromSingleton" Test.Kore.Builtin.Map.test_unifySelectSingletonFromSingleton

    t282 <- testGroup "unifySelectFromSingletonWithoutLeftovers" Test.Kore.Builtin.Map.test_unifySelectFromSingletonWithoutLeftovers

    t283 <- testGroup "unifySelectFromTwoElementMap" Test.Kore.Builtin.Map.test_unifySelectFromTwoElementMap

    t284 <- testGroup "unifySelectTwoFromTwoElementMap" Test.Kore.Builtin.Map.test_unifySelectTwoFromTwoElementMap

    t285 <- testGroup "unifySameSymbolicKey" Test.Kore.Builtin.Map.test_unifySameSymbolicKey

    t286 <- testGroup "unifySameSymbolicKeySymbolicOpaque" Test.Kore.Builtin.Map.test_unifySameSymbolicKeySymbolicOpaque

    t287 <- testGroup "concretizeKeys" Test.Kore.Builtin.Map.test_concretizeKeys

    t288 <- testGroup "renormalize" Test.Kore.Builtin.Map.test_renormalize

    t289 <- testGroup "concretizeKeysAxiom" Test.Kore.Builtin.Map.test_concretizeKeysAxiom

    t290 <- pure $ H.testProperty "unparse" Test.Kore.Builtin.Map.hprop_unparse

    t291 <- testGroup "inKeys" Test.Kore.Builtin.Map.test_inKeys

    t292 <- testGroup "unit" Test.Kore.Builtin.Set.test_unit

    t293 <- testGroup "getUnit" Test.Kore.Builtin.Set.test_getUnit

    t294 <- testGroup "inElement" Test.Kore.Builtin.Set.test_inElement

    t295 <- testGroup "inUnitSymbolic" Test.Kore.Builtin.Set.test_inUnitSymbolic

    t296 <- testGroup "inElementSymbolic" Test.Kore.Builtin.Set.test_inElementSymbolic

    t297 <- testGroup "inConcat" Test.Kore.Builtin.Set.test_inConcat

    t298 <- testGroup "inConcatSymbolic" Test.Kore.Builtin.Set.test_inConcatSymbolic

    t299 <- testGroup "concatUnit" Test.Kore.Builtin.Set.test_concatUnit

    t300 <- testGroup "concatAssociates" Test.Kore.Builtin.Set.test_concatAssociates

    t301 <- testGroup "concatNormalizes" Test.Kore.Builtin.Set.test_concatNormalizes

    t302 <- testGroup "difference" Test.Kore.Builtin.Set.test_difference

    t303 <- testGroup "difference symbolic" Test.Kore.Builtin.Set.test_difference_symbolic

    t304 <- testGroup "toList" Test.Kore.Builtin.Set.test_toList

    t305 <- testGroup "size" Test.Kore.Builtin.Set.test_size

    t306 <- testGroup "intersection unit" Test.Kore.Builtin.Set.test_intersection_unit

    t307 <- testGroup "intersection idem" Test.Kore.Builtin.Set.test_intersection_idem

    t308 <- testGroup "list2set" Test.Kore.Builtin.Set.test_list2set

    t309 <- testGroup "inclusion" Test.Kore.Builtin.Set.test_inclusion

    t310 <- testGroup "symbolic" Test.Kore.Builtin.Set.test_symbolic

    t311 <- testGroup "unifyConcreteIdem" Test.Kore.Builtin.Set.test_unifyConcreteIdem

    t312 <- testGroup "unifyConcreteDistinct" Test.Kore.Builtin.Set.test_unifyConcreteDistinct

    t313 <- testGroup "unifyFramingVariable" Test.Kore.Builtin.Set.test_unifyFramingVariable

    t314 <- testGroup "unifySelectFromEmpty" Test.Kore.Builtin.Set.test_unifySelectFromEmpty

    t315 <- testGroup "unifySelectFromSingleton" Test.Kore.Builtin.Set.test_unifySelectFromSingleton

    t316 <- testGroup "unifySelectFromSingletonWithoutLeftovers" Test.Kore.Builtin.Set.test_unifySelectFromSingletonWithoutLeftovers

    t317 <- testGroup "unifySelectFromTwoElementSet" Test.Kore.Builtin.Set.test_unifySelectFromTwoElementSet

    t318 <- testGroup "unifySelectTwoFromTwoElementSet" Test.Kore.Builtin.Set.test_unifySelectTwoFromTwoElementSet

    t319 <- testGroup "unifyConcatElemVarVsElemSet" Test.Kore.Builtin.Set.test_unifyConcatElemVarVsElemSet

    t320 <- testGroup "unifyConcatElemVarVsElemElem" Test.Kore.Builtin.Set.test_unifyConcatElemVarVsElemElem

    t321 <- testGroup "unifyConcatElemElemVsElemConcrete" Test.Kore.Builtin.Set.test_unifyConcatElemElemVsElemConcrete

    t322 <- testGroup "unifyConcatElemElemVsElemElem" Test.Kore.Builtin.Set.test_unifyConcatElemElemVsElemElem

    t323 <- testGroup "unifyConcatElemConcatVsElemConcrete" Test.Kore.Builtin.Set.test_unifyConcatElemConcatVsElemConcrete

    t324 <- testGroup "unifyConcatElemConcreteVsElemConcrete1" Test.Kore.Builtin.Set.test_unifyConcatElemConcreteVsElemConcrete1

    t325 <- testGroup "unifyConcatElemConcreteVsElemConcrete2" Test.Kore.Builtin.Set.test_unifyConcatElemConcreteVsElemConcrete2

    t326 <- testGroup "unifyConcatElemConcreteVsElemConcrete3" Test.Kore.Builtin.Set.test_unifyConcatElemConcreteVsElemConcrete3

    t327 <- testGroup "unifyConcatElemConcreteVsElemConcrete4" Test.Kore.Builtin.Set.test_unifyConcatElemConcreteVsElemConcrete4

    t328 <- testGroup "unifyConcatElemConcreteVsElemConcrete5" Test.Kore.Builtin.Set.test_unifyConcatElemConcreteVsElemConcrete5

    t329 <- testGroup "unifyConcatElemVsElem" Test.Kore.Builtin.Set.test_unifyConcatElemVsElem

    t330 <- testGroup "unifyConcatElemVsElemConcrete1" Test.Kore.Builtin.Set.test_unifyConcatElemVsElemConcrete1

    t331 <- testGroup "unifyConcatElemVsElemConcrete2" Test.Kore.Builtin.Set.test_unifyConcatElemVsElemConcrete2

    t332 <- testGroup "unifyConcatElemVsElemElem" Test.Kore.Builtin.Set.test_unifyConcatElemVsElemElem

    t333 <- testGroup "unifyConcatElemVsElemConcat" Test.Kore.Builtin.Set.test_unifyConcatElemVsElemConcat

    t334 <- testGroup "unifyConcatElemVsElemVar" Test.Kore.Builtin.Set.test_unifyConcatElemVsElemVar

    t335 <- testGroup "unifyConcatElemElemVsElemConcat" Test.Kore.Builtin.Set.test_unifyConcatElemElemVsElemConcat

    t336 <- testGroup "unifyConcatElemElemVsElemConcatSet" Test.Kore.Builtin.Set.test_unifyConcatElemElemVsElemConcatSet

    t337 <- testGroup "unifyFnSelectFromSingleton" Test.Kore.Builtin.Set.test_unifyFnSelectFromSingleton

    t338 <- testGroup "unify concat xSet unit unit vs unit" Test.Kore.Builtin.Set.test_unify_concat_xSet_unit_unit_vs_unit

    t339 <- testGroup "unifyMultipleIdenticalOpaqueSets" Test.Kore.Builtin.Set.test_unifyMultipleIdenticalOpaqueSets

    t340 <- testGroup "concretizeKeys" Test.Kore.Builtin.Set.test_concretizeKeys

    t341 <- testGroup "concretizeKeysAxiom" Test.Kore.Builtin.Set.test_concretizeKeysAxiom

    t342 <- testGroup "isBuiltin" Test.Kore.Builtin.Set.test_isBuiltin

    t343 <- pure $ H.testProperty "unparse" Test.Kore.Builtin.Set.hprop_unparse

    t344 <- testGroup "verify" Test.Kore.Builtin.Endianness.test_verify

    t345 <- testGroup "match" Test.Kore.Builtin.Endianness.test_match

    t346 <- testGroup "unify" Test.Kore.Builtin.Endianness.test_unify

    t347 <- testGroup "gt" Test.Kore.Builtin.Int.test_gt

    t348 <- testGroup "ge" Test.Kore.Builtin.Int.test_ge

    t349 <- testGroup "eq" Test.Kore.Builtin.Int.test_eq

    t350 <- testGroup "le" Test.Kore.Builtin.Int.test_le

    t351 <- testGroup "lt" Test.Kore.Builtin.Int.test_lt

    t352 <- testGroup "ne" Test.Kore.Builtin.Int.test_ne

    t353 <- testGroup "min" Test.Kore.Builtin.Int.test_min

    t354 <- testGroup "max" Test.Kore.Builtin.Int.test_max

    t355 <- testGroup "add" Test.Kore.Builtin.Int.test_add

    t356 <- testGroup "sub" Test.Kore.Builtin.Int.test_sub

    t357 <- testGroup "mul" Test.Kore.Builtin.Int.test_mul

    t358 <- testGroup "abs" Test.Kore.Builtin.Int.test_abs

    t359 <- testGroup "tdiv" Test.Kore.Builtin.Int.test_tdiv

    t360 <- testGroup "tmod" Test.Kore.Builtin.Int.test_tmod

    t361 <- testGroup "tdivZero" Test.Kore.Builtin.Int.test_tdivZero

    t362 <- testGroup "tmodZero" Test.Kore.Builtin.Int.test_tmodZero

    t363 <- testGroup "ediv property" Test.Kore.Builtin.Int.test_ediv_property

    t364 <- testGroup "emod property" Test.Kore.Builtin.Int.test_emod_property

    t365 <- testGroup "edivZero" Test.Kore.Builtin.Int.test_edivZero

    t366 <- testGroup "emodZero" Test.Kore.Builtin.Int.test_emodZero

    t367 <- testGroup "ediv" Test.Kore.Builtin.Int.test_ediv

    t368 <- testGroup "emod" Test.Kore.Builtin.Int.test_emod

    t369 <- testGroup "euclidian division theorem" Test.Kore.Builtin.Int.test_euclidian_division_theorem

    t370 <- testGroup "and" Test.Kore.Builtin.Int.test_and

    t371 <- testGroup "or" Test.Kore.Builtin.Int.test_or

    t372 <- testGroup "xor" Test.Kore.Builtin.Int.test_xor

    t373 <- testGroup "not" Test.Kore.Builtin.Int.test_not

    t374 <- testGroup "shl" Test.Kore.Builtin.Int.test_shl

    t375 <- testGroup "shr" Test.Kore.Builtin.Int.test_shr

    t376 <- testGroup "pow" Test.Kore.Builtin.Int.test_pow

    t377 <- testGroup "powmod" Test.Kore.Builtin.Int.test_powmod

    t378 <- testGroup "log2" Test.Kore.Builtin.Int.test_log2

    t379 <- testGroup "unifyEqual NotEqual" Test.Kore.Builtin.Int.test_unifyEqual_NotEqual

    t380 <- testGroup "unifyEqual Equal" Test.Kore.Builtin.Int.test_unifyEqual_Equal

    t381 <- testGroup "unifyAnd NotEqual" Test.Kore.Builtin.Int.test_unifyAnd_NotEqual

    t382 <- testGroup "unifyAnd Equal" Test.Kore.Builtin.Int.test_unifyAnd_Equal

    t383 <- testGroup "unifyAndEqual Equal" Test.Kore.Builtin.Int.test_unifyAndEqual_Equal

    t384 <- testGroup "unifyAnd Fn" Test.Kore.Builtin.Int.test_unifyAnd_Fn

    t385 <- testGroup "reflexivity symbolic" Test.Kore.Builtin.Int.test_reflexivity_symbolic

    t386 <- testGroup "symbolic eq not conclusive" Test.Kore.Builtin.Int.test_symbolic_eq_not_conclusive

    t387 <- testGroup "unifyIntEq" Test.Kore.Builtin.Int.test_unifyIntEq

    t388 <- pure $ H.testProperty "unparse" Test.Kore.Builtin.Int.hprop_unparse

    t389 <- testGroup "contradiction" Test.Kore.Builtin.Int.test_contradiction

    t390 <- testGroup "keq" Test.Kore.Builtin.KEqual.test_keq

    t391 <- testGroup "kneq" Test.Kore.Builtin.KEqual.test_kneq

    t392 <- testGroup "KEqual" Test.Kore.Builtin.KEqual.test_KEqual

    t393 <- testGroup "KIte" Test.Kore.Builtin.KEqual.test_KIte

    t394 <- testGroup "KEqualSimplification" Test.Kore.Builtin.KEqual.test_KEqualSimplification

    t395 <- testGroup "getUnit" Test.Kore.Builtin.List.test_getUnit

    t396 <- testGroup "getFirstElement" Test.Kore.Builtin.List.test_getFirstElement

    t397 <- testGroup "getLastElement" Test.Kore.Builtin.List.test_getLastElement

    t398 <- testGroup "GetUpdate" Test.Kore.Builtin.List.test_GetUpdate

    t399 <- testGroup "concatUnit" Test.Kore.Builtin.List.test_concatUnit

    t400 <- testGroup "concatUnitSymbolic" Test.Kore.Builtin.List.test_concatUnitSymbolic

    t401 <- testGroup "concatAssociates" Test.Kore.Builtin.List.test_concatAssociates

    t402 <- testGroup "concatSymbolic" Test.Kore.Builtin.List.test_concatSymbolic

    t403 <- testGroup "concatSymbolicDifferentLengths" Test.Kore.Builtin.List.test_concatSymbolicDifferentLengths

    t404 <- testGroup "simplify" Test.Kore.Builtin.List.test_simplify

    t405 <- testGroup "isBuiltin" Test.Kore.Builtin.List.test_isBuiltin

    t406 <- testGroup "inUnit" Test.Kore.Builtin.List.test_inUnit

    t407 <- testGroup "inElement" Test.Kore.Builtin.List.test_inElement

    t408 <- testGroup "inConcat" Test.Kore.Builtin.List.test_inConcat

    t409 <- testGroup "make" Test.Kore.Builtin.List.test_make

    t410 <- testGroup "updateAll" Test.Kore.Builtin.List.test_updateAll

    t411 <- pure $ H.testProperty "unparse" Test.Kore.Builtin.List.hprop_unparse

    t412 <- testGroup "size" Test.Kore.Builtin.List.test_size

    t413 <- pure $ H.testProperty "Builtin Map" Test.Kore.Builtin.AssocComm.CeilSimplifier.hprop_Builtin_Map

    t414 <- pure $ H.testProperty "Builtin Set" Test.Kore.Builtin.AssocComm.CeilSimplifier.hprop_Builtin_Set

    t415 <- testGroup "Builtin Map" Test.Kore.Builtin.AssocComm.CeilSimplifier.test_Builtin_Map

    t416 <- testGroup "Builtin Set" Test.Kore.Builtin.AssocComm.CeilSimplifier.test_Builtin_Set

    t417 <- testGroup "productionID" Test.Kore.Attribute.ProductionID.test_productionID

    t418 <- testGroup "Attributes" Test.Kore.Attribute.ProductionID.test_Attributes

    t419 <- testGroup "duplicate" Test.Kore.Attribute.ProductionID.test_duplicate

    t420 <- testGroup "zeroArguments" Test.Kore.Attribute.ProductionID.test_zeroArguments

    t421 <- testGroup "twoArguments" Test.Kore.Attribute.ProductionID.test_twoArguments

    t422 <- testGroup "parameters" Test.Kore.Attribute.ProductionID.test_parameters

    t423 <- testGroup "trusted" Test.Kore.Attribute.Trusted.test_trusted

    t424 <- testGroup "Attributes" Test.Kore.Attribute.Trusted.test_Attributes

    t425 <- testGroup "duplicate" Test.Kore.Attribute.Trusted.test_duplicate

    t426 <- testGroup "arguments" Test.Kore.Attribute.Trusted.test_arguments

    t427 <- testGroup "parameters" Test.Kore.Attribute.Trusted.test_parameters

    t428 <- testGroup "simplification" Test.Kore.Attribute.Simplification.test_simplification

    t429 <- testGroup "simplification with argument" Test.Kore.Attribute.Simplification.test_simplification_with_argument

    t430 <- testGroup "simplification with empty argument" Test.Kore.Attribute.Simplification.test_simplification_with_empty_argument

    t431 <- testGroup "Attributes" Test.Kore.Attribute.Simplification.test_Attributes

    t432 <- testGroup "Attributes with argument" Test.Kore.Attribute.Simplification.test_Attributes_with_argument

    t433 <- testGroup "duplicate" Test.Kore.Attribute.Simplification.test_duplicate

    t434 <- testGroup "arguments wrong type" Test.Kore.Attribute.Simplification.test_arguments_wrong_type

    t435 <- testGroup "multiple arguments" Test.Kore.Attribute.Simplification.test_multiple_arguments

    t436 <- testGroup "parameters" Test.Kore.Attribute.Simplification.test_parameters

    t437 <- testGroup "UniqueId" Test.Kore.Attribute.UniqueId.test_UniqueId

    t438 <- testGroup "Attributes" Test.Kore.Attribute.UniqueId.test_Attributes

    t439 <- testGroup "duplicate" Test.Kore.Attribute.UniqueId.test_duplicate

    t440 <- testGroup "arguments" Test.Kore.Attribute.UniqueId.test_arguments

    t441 <- testGroup "parameters" Test.Kore.Attribute.UniqueId.test_parameters

    t442 <- testGroup "sortInjection" Test.Kore.Attribute.SortInjection.test_sortInjection

    t443 <- testGroup "Attributes" Test.Kore.Attribute.SortInjection.test_Attributes

    t444 <- testGroup "duplicate" Test.Kore.Attribute.SortInjection.test_duplicate

    t445 <- testGroup "arguments" Test.Kore.Attribute.SortInjection.test_arguments

    t446 <- testGroup "parameters" Test.Kore.Attribute.SortInjection.test_parameters

    t447 <- testGroup "functional" Test.Kore.Attribute.Functional.test_functional

    t448 <- testGroup "Attributes" Test.Kore.Attribute.Functional.test_Attributes

    t449 <- testGroup "duplicate" Test.Kore.Attribute.Functional.test_duplicate

    t450 <- testGroup "parameters" Test.Kore.Attribute.Functional.test_parameters

    t451 <- testGroup "arguments" Test.Kore.Attribute.Functional.test_arguments

    t452 <- testGroup "owise" Test.Kore.Attribute.Owise.test_owise

    t453 <- testGroup "attributes" Test.Kore.Attribute.Owise.test_attributes

    t454 <- testGroup "parameters" Test.Kore.Attribute.Owise.test_parameters

    t455 <- testGroup "duplicate" Test.Kore.Attribute.Owise.test_duplicate

    t456 <- testGroup "arguments" Test.Kore.Attribute.Owise.test_arguments

    t457 <- testGroup "hook" Test.Kore.Attribute.Hook.test_hook

    t458 <- testGroup "Attributes" Test.Kore.Attribute.Hook.test_Attributes

    t459 <- testGroup "duplicate" Test.Kore.Attribute.Hook.test_duplicate

    t460 <- testGroup "zeroArguments" Test.Kore.Attribute.Hook.test_zeroArguments

    t461 <- testGroup "twoArguments" Test.Kore.Attribute.Hook.test_twoArguments

    t462 <- testGroup "parameters" Test.Kore.Attribute.Hook.test_parameters

    t463 <- testGroup "Label" Test.Kore.Attribute.Label.test_Label

    t464 <- testGroup "Attributes" Test.Kore.Attribute.Label.test_Attributes

    t465 <- testGroup "duplicate" Test.Kore.Attribute.Label.test_duplicate

    t466 <- testGroup "arguments" Test.Kore.Attribute.Label.test_arguments

    t467 <- testGroup "parameters" Test.Kore.Attribute.Label.test_parameters

    t468 <- testGroup "Overload" Test.Kore.Attribute.Overload.test_Overload

    t469 <- testGroup "Attributes" Test.Kore.Attribute.Overload.test_Attributes

    t470 <- testGroup "duplicate" Test.Kore.Attribute.Overload.test_duplicate

    t471 <- testGroup "arguments" Test.Kore.Attribute.Overload.test_arguments

    t472 <- testGroup "parameters" Test.Kore.Attribute.Overload.test_parameters

    t473 <- testGroup "dont ignore" Test.Kore.Attribute.Overload.test_dont_ignore

    t474 <- testGroup "subsort" Test.Kore.Attribute.Subsort.test_subsort

    t475 <- testGroup "Attributes" Test.Kore.Attribute.Subsort.test_Attributes

    t476 <- testGroup "zeroParams" Test.Kore.Attribute.Subsort.test_zeroParams

    t477 <- testGroup "arguments" Test.Kore.Attribute.Subsort.test_arguments

    t478 <- testGroup "extracted smtlib" Test.Kore.Attribute.Smtlib.test_extracted_smtlib

    t479 <- testGroup "extracted smthook" Test.Kore.Attribute.Smtlib.test_extracted_smthook

    t480 <- testGroup "fill SExpr templates" Test.Kore.Attribute.Smtlib.test_fill_SExpr_templates

    t481 <- testGroup "constructor" Test.Kore.Attribute.Constructor.test_constructor

    t482 <- testGroup "Attributes" Test.Kore.Attribute.Constructor.test_Attributes

    t483 <- testGroup "duplicate" Test.Kore.Attribute.Constructor.test_duplicate

    t484 <- testGroup "arguments" Test.Kore.Attribute.Constructor.test_arguments

    t485 <- testGroup "parameters" Test.Kore.Attribute.Constructor.test_parameters

    t486 <- testGroup "stepperAttributes" Test.Kore.Attribute.Symbol.test_stepperAttributes

    t487 <- testGroup "Anywhere" Test.Kore.Attribute.Symbol.test_Anywhere

    t488 <- testGroup "Memo" Test.Kore.Attribute.Symbol.test_Memo

    t489 <- testGroup "Klabel" Test.Kore.Attribute.Symbol.test_Klabel

    t490 <- testGroup "SymbolKywd" Test.Kore.Attribute.Symbol.test_SymbolKywd

    t491 <- testGroup "NoEvaluators" Test.Kore.Attribute.Symbol.test_NoEvaluators

    t492 <- testGroup "injective" Test.Kore.Attribute.Injective.test_injective

    t493 <- testGroup "Attributes" Test.Kore.Attribute.Injective.test_Attributes

    t494 <- testGroup "duplicate" Test.Kore.Attribute.Injective.test_duplicate

    t495 <- testGroup "arguments" Test.Kore.Attribute.Injective.test_arguments

    t496 <- testGroup "parameters" Test.Kore.Attribute.Injective.test_parameters

    t497 <- testGroup "nonExecutable" Test.Kore.Attribute.NonExecutable.test_nonExecutable

    t498 <- testGroup "Attributes" Test.Kore.Attribute.NonExecutable.test_Attributes

    t499 <- testGroup "duplicate" Test.Kore.Attribute.NonExecutable.test_duplicate

    t500 <- testGroup "parameters" Test.Kore.Attribute.NonExecutable.test_parameters

    t501 <- testGroup "arguments" Test.Kore.Attribute.NonExecutable.test_arguments

    t502 <- testGroup "idem" Test.Kore.Attribute.Idem.test_idem

    t503 <- testGroup "Attributes" Test.Kore.Attribute.Idem.test_Attributes

    t504 <- testGroup "duplicate" Test.Kore.Attribute.Idem.test_duplicate

    t505 <- testGroup "arguments" Test.Kore.Attribute.Idem.test_arguments

    t506 <- testGroup "parameters" Test.Kore.Attribute.Idem.test_parameters

    t507 <- testGroup "comm" Test.Kore.Attribute.Comm.test_comm

    t508 <- testGroup "Attributes" Test.Kore.Attribute.Comm.test_Attributes

    t509 <- testGroup "duplicate" Test.Kore.Attribute.Comm.test_duplicate

    t510 <- testGroup "arguments" Test.Kore.Attribute.Comm.test_arguments

    t511 <- testGroup "parameters" Test.Kore.Attribute.Comm.test_parameters

    t512 <- testGroup "function" Test.Kore.Attribute.Function.test_function

    t513 <- testGroup "Attributes" Test.Kore.Attribute.Function.test_Attributes

    t514 <- testGroup "duplicate" Test.Kore.Attribute.Function.test_duplicate

    t515 <- testGroup "arguments" Test.Kore.Attribute.Function.test_arguments

    t516 <- testGroup "parameters" Test.Kore.Attribute.Function.test_parameters

    t517 <- testGroup "priority" Test.Kore.Attribute.Priority.test_priority

    t518 <- testGroup "Attributes" Test.Kore.Attribute.Priority.test_Attributes

    t519 <- testGroup "duplicate" Test.Kore.Attribute.Priority.test_duplicate

    t520 <- testGroup "zeroArguments" Test.Kore.Attribute.Priority.test_zeroArguments

    t521 <- testGroup "twoArguments" Test.Kore.Attribute.Priority.test_twoArguments

    t522 <- testGroup "negative" Test.Kore.Attribute.Priority.test_negative

    t523 <- testGroup "assoc" Test.Kore.Attribute.Assoc.test_assoc

    t524 <- testGroup "Attributes" Test.Kore.Attribute.Assoc.test_Attributes

    t525 <- testGroup "duplicate" Test.Kore.Attribute.Assoc.test_duplicate

    t526 <- testGroup "arguments" Test.Kore.Attribute.Assoc.test_arguments

    t527 <- testGroup "parameters" Test.Kore.Attribute.Assoc.test_parameters

    t528 <- testGroup "Synthetic" Test.Kore.Attribute.Pattern.FreeVariables.test_Synthetic

    t529 <- testGroup "instance Synthetic TermLike" Test.Kore.Attribute.Pattern.FreeVariables.test_instance_Synthetic_TermLike

    t530 <- testGroup "concat" Test.Kore.Attribute.Pattern.FreeVariables.test_concat

    t531 <- testGroup "instance Synthetic" Test.Kore.Attribute.Pattern.Functional.test_instance_Synthetic

    t532 <- testGroup "TermLike" Test.Kore.Attribute.Pattern.ConstructorLike.test_TermLike

    t533 <- testGroup "instance Synthetic" Test.Kore.Attribute.Pattern.Sort.test_instance_Synthetic

    t534 <- testGroup "instance Synthetic" Test.Kore.Attribute.Pattern.Defined.test_instance_Synthetic

    t535 <- testGroup "instance Synthetic" Test.Kore.Attribute.Pattern.Function.test_instance_Synthetic

    t536 <- testGroup "sortParsing" Test.Kore.Attribute.Sort.ConstructorsBuilder.test_sortParsing

    t537 <- testGroup "HasDomainValues" Test.Kore.Attribute.Sort.HasDomainValues.test_HasDomainValues

    t538 <- testGroup "Attributes" Test.Kore.Attribute.Sort.HasDomainValues.test_Attributes

    t539 <- testGroup "duplicate" Test.Kore.Attribute.Sort.HasDomainValues.test_duplicate

    t540 <- testGroup "arity" Test.Kore.Attribute.Sort.HasDomainValues.test_arity

    t541 <- testGroup "arguments" Test.Kore.Attribute.Sort.HasDomainValues.test_arguments

    t542 <- testGroup "parameters" Test.Kore.Attribute.Sort.HasDomainValues.test_parameters

    t543 <- testGroup "Unit" Test.Kore.Attribute.Sort.Unit.test_Unit

    t544 <- testGroup "Attributes" Test.Kore.Attribute.Sort.Unit.test_Attributes

    t545 <- testGroup "duplicate" Test.Kore.Attribute.Sort.Unit.test_duplicate

    t546 <- testGroup "arity" Test.Kore.Attribute.Sort.Unit.test_arity

    t547 <- testGroup "arguments" Test.Kore.Attribute.Sort.Unit.test_arguments

    t548 <- testGroup "parameters" Test.Kore.Attribute.Sort.Unit.test_parameters

    t549 <- testGroup "unit" Test.Kore.Attribute.Axiom.Unit.test_unit

    t550 <- testGroup "Attributes" Test.Kore.Attribute.Axiom.Unit.test_Attributes

    t551 <- testGroup "duplicate" Test.Kore.Attribute.Axiom.Unit.test_duplicate

    t552 <- testGroup "arguments" Test.Kore.Attribute.Axiom.Unit.test_arguments

    t553 <- testGroup "parameters" Test.Kore.Attribute.Axiom.Unit.test_parameters

    t554 <- testGroup "concrete" Test.Kore.Attribute.Axiom.Concrete.test_concrete

    t555 <- testGroup "concrete select" Test.Kore.Attribute.Axiom.Concrete.test_concrete_select

    t556 <- testGroup "concrete selectx2" Test.Kore.Attribute.Axiom.Concrete.test_concrete_selectx2

    t557 <- testGroup "Attributes" Test.Kore.Attribute.Axiom.Concrete.test_Attributes

    t558 <- testGroup "parameters" Test.Kore.Attribute.Axiom.Concrete.test_parameters

    t559 <- testGroup "duplicate" Test.Kore.Attribute.Axiom.Concrete.test_duplicate

    t560 <- testGroup "duplicate2" Test.Kore.Attribute.Axiom.Concrete.test_duplicate2

    t561 <- testGroup "duplicate3" Test.Kore.Attribute.Axiom.Concrete.test_duplicate3

    t562 <- testGroup "notfree" Test.Kore.Attribute.Axiom.Concrete.test_notfree

    t563 <- testGroup "arguments" Test.Kore.Attribute.Axiom.Concrete.test_arguments

    t564 <- testGroup "symbolic" Test.Kore.Attribute.Axiom.Symbolic.test_symbolic

    t565 <- testGroup "symbolic select" Test.Kore.Attribute.Axiom.Symbolic.test_symbolic_select

    t566 <- testGroup "symbolic selectx2" Test.Kore.Attribute.Axiom.Symbolic.test_symbolic_selectx2

    t567 <- testGroup "Attributes" Test.Kore.Attribute.Axiom.Symbolic.test_Attributes

    t568 <- testGroup "parameters" Test.Kore.Attribute.Axiom.Symbolic.test_parameters

    t569 <- testGroup "duplicate" Test.Kore.Attribute.Axiom.Symbolic.test_duplicate

    t570 <- testGroup "duplicate2" Test.Kore.Attribute.Axiom.Symbolic.test_duplicate2

    t571 <- testGroup "duplicate3" Test.Kore.Attribute.Axiom.Symbolic.test_duplicate3

    t572 <- testGroup "notfree" Test.Kore.Attribute.Axiom.Symbolic.test_notfree

    t573 <- testGroup "arguments" Test.Kore.Attribute.Axiom.Symbolic.test_arguments

    t574 <- testGroup "noEvaluators" Test.Kore.Attribute.Symbol.NoEvaluators.test_noEvaluators

    t575 <- testGroup "Attributes" Test.Kore.Attribute.Symbol.NoEvaluators.test_Attributes

    t576 <- testGroup "duplicate" Test.Kore.Attribute.Symbol.NoEvaluators.test_duplicate

    t577 <- testGroup "arguments" Test.Kore.Attribute.Symbol.NoEvaluators.test_arguments

    t578 <- testGroup "parameters" Test.Kore.Attribute.Symbol.NoEvaluators.test_parameters

    t579 <- testGroup "Klabel" Test.Kore.Attribute.Symbol.Klabel.test_Klabel

    t580 <- testGroup "anywhere" Test.Kore.Attribute.Symbol.Anywhere.test_anywhere

    t581 <- testGroup "Attributes" Test.Kore.Attribute.Symbol.Anywhere.test_Attributes

    t582 <- testGroup "duplicate" Test.Kore.Attribute.Symbol.Anywhere.test_duplicate

    t583 <- testGroup "arguments" Test.Kore.Attribute.Symbol.Anywhere.test_arguments

    t584 <- testGroup "parameters" Test.Kore.Attribute.Symbol.Anywhere.test_parameters

    t585 <- testGroup "memo" Test.Kore.Attribute.Symbol.Memo.test_memo

    t586 <- testGroup "Attributes" Test.Kore.Attribute.Symbol.Memo.test_Attributes

    t587 <- testGroup "duplicate" Test.Kore.Attribute.Symbol.Memo.test_duplicate

    t588 <- testGroup "arguments" Test.Kore.Attribute.Symbol.Memo.test_arguments

    t589 <- testGroup "parameters" Test.Kore.Attribute.Symbol.Memo.test_parameters

    t590 <- testGroup "symbolKywd" Test.Kore.Attribute.Symbol.SymbolKywd.test_symbolKywd

    t591 <- testGroup "Attributes" Test.Kore.Attribute.Symbol.SymbolKywd.test_Attributes

    t592 <- testGroup "duplicate" Test.Kore.Attribute.Symbol.SymbolKywd.test_duplicate

    t593 <- testGroup "arguments" Test.Kore.Attribute.Symbol.SymbolKywd.test_arguments

    t594 <- testGroup "parameters" Test.Kore.Attribute.Symbol.SymbolKywd.test_parameters

    t595 <- testGroup "Id" Test.Kore.Syntax.Id.test_Id

    t596 <- testGroup "isSetVariable" Test.Kore.Syntax.Variable.test_isSetVariable

    t597 <- testGroup "isElementVariable" Test.Kore.Syntax.Variable.test_isElementVariable

    t598 <- pure $ H.testProperty "instance Injection SomeVariableName ElementVariableName" Test.Kore.Syntax.Variable.hprop_instance_Injection_SomeVariableName_ElementVariableName

    t599 <- pure $ H.testProperty "instance Injection SomeVariableName SetVariableName" Test.Kore.Syntax.Variable.hprop_instance_Injection_SomeVariableName_SetVariableName

    t600 <- testGroup "JsonRoundTrips" Test.Kore.Syntax.Json.test_JsonRoundTrips

    t601 <- testGroup "Unit tests for json failure modes" Test.Kore.Syntax.Json.test_Unit_tests_for_json_failure_modes

    t602 <- testGroup "headerFailures" Test.Kore.Syntax.Json.test_headerFailures

    t603 <- testGroup "ParserKoreFiles" Test.Kore.Syntax.Json.Roundtrips.test_ParserKoreFiles

    t604 <- testGroup "isOverloaded" Test.Kore.IndexedModule.OverloadGraph.test_isOverloaded

    t605 <- testGroup "isOverloading" Test.Kore.IndexedModule.OverloadGraph.test_isOverloading

    t606 <- testGroup "commonOverloads" Test.Kore.IndexedModule.OverloadGraph.test_commonOverloads

    t607 <- testGroup "fromIndexedModule" Test.Kore.IndexedModule.OverloadGraph.test_fromIndexedModule

    t608 <- testGroup "resolvers" Test.Kore.IndexedModule.Resolvers.test_resolvers

    t609 <- testGroup "resolver undefined messages" Test.Kore.IndexedModule.Resolvers.test_resolver_undefined_messages

    t610 <- testGroup "isSubsortOf" Test.Kore.IndexedModule.SortGraph.test_isSubsortOf

    t611 <- testGroup "subsortsOf" Test.Kore.IndexedModule.SortGraph.test_subsortsOf

    t612 <- testGroup "fromIndexedModule" Test.Kore.IndexedModule.SortGraph.test_fromIndexedModule

    t613 <- testGroup "undefineds" Test.Kore.IndexedModule.Error.test_undefineds

    t614 <- testGroup "refreshVariable" Test.Kore.Variables.Fresh.test_refreshVariable

    t615 <- testGroup "FreshPartialOrd VariableName" Test.Kore.Variables.Fresh.test_FreshPartialOrd_VariableName

    t616 <- testGroup "FreshPartialOrd ElementVariableName" Test.Kore.Variables.Fresh.test_FreshPartialOrd_ElementVariableName

    t617 <- testGroup "FreshPartialOrd SetVariableName" Test.Kore.Variables.Fresh.test_FreshPartialOrd_SetVariableName

    t618 <- testGroup "FreshPartialOrd SomeVariableName" Test.Kore.Variables.Fresh.test_FreshPartialOrd_SomeVariableName

    t619 <- testGroup "Eq" Test.Kore.Variables.Target.test_Eq

    t620 <- testGroup "Ord" Test.Kore.Variables.Target.test_Ord

    t621 <- testGroup "Hashable" Test.Kore.Variables.Target.test_Hashable

    t622 <- testGroup "FreshPartialOrd" Test.Kore.Variables.Target.test_FreshPartialOrd

    t623 <- testGroup "FreshName" Test.Kore.Variables.Target.test_FreshName

    t624 <- testGroup "mergeAndNormalizeSubstitutions" Test.Kore.Unification.UnifierT.test_mergeAndNormalizeSubstitutions

    t625 <- testGroup "simplifyCondition" Test.Kore.Unification.UnifierT.test_simplifyCondition

    t626 <- testGroup "unification" Test.Kore.Unification.Unifier.test_unification

    t627 <- testGroup "unsupportedConstructs" Test.Kore.Unification.Unifier.test_unsupportedConstructs

    t628 <- testGroup "normalize" Test.Kore.Unification.SubstitutionNormalization.test_normalize

    t629 <- testGroup "substitution" Test.Kore.Internal.Substitution.test_substitution

    t630 <- testGroup "toPredicate" Test.Kore.Internal.Substitution.test_toPredicate

    t631 <- testGroup "substitute" Test.Kore.Internal.Substitution.test_substitute

    t632 <- testGroup "retractAssignmentFor" Test.Kore.Internal.Substitution.test_retractAssignmentFor

    t633 <- testGroup "multiAndTopBottom" Test.Kore.Internal.MultiAnd.test_multiAndTopBottom

    t634 <- testGroup "make" Test.Kore.Internal.MultiAnd.test_make

    t635 <- testGroup "Predicate" Test.Kore.Internal.From.test_Predicate

    t636 <- testGroup "symbolOrAliasSorts" Test.Kore.Internal.ApplicationSorts.test_symbolOrAliasSorts

    t637 <- testGroup "assumeDefined" Test.Kore.Internal.SideCondition.test_assumeDefined

    t638 <- testGroup "isDefined" Test.Kore.Internal.SideCondition.test_isDefined

    t639 <- testGroup "generateNormalizedAcs" Test.Kore.Internal.SideCondition.test_generateNormalizedAcs

    t640 <- testGroup "cacheSimplifiedFunctions" Test.Kore.Internal.SideCondition.test_cacheSimplifiedFunctions

    t641 <- pure $ H.testProperty "mergeIdemOr" Test.Kore.Internal.OrPattern.hprop_mergeIdemOr

    t642 <- pure $ H.testProperty "makeIdemOr" Test.Kore.Internal.OrPattern.hprop_makeIdemOr

    t643 <- pure $ H.testProperty "flattenIdemOr" Test.Kore.Internal.OrPattern.hprop_flattenIdemOr

    t644 <- testGroup "distributeAnd" Test.Kore.Internal.OrPattern.test_distributeAnd

    t645 <- testGroup "distributeApplication" Test.Kore.Internal.OrPattern.test_distributeApplication

    t646 <- testGroup "retractKey" Test.Kore.Internal.Key.test_retractKey

    t647 <- testGroup "predicate" Test.Kore.Internal.Predicate.test_predicate

    t648 <- testGroup "mapVariables" Test.Kore.Internal.Predicate.test_mapVariables

    t649 <- testGroup "refresh" Test.Kore.Internal.MultiExists.test_refresh

    t650 <- testGroup "filterRelevant" Test.Kore.Internal.MultiExists.test_filterRelevant

    t651 <- testGroup "Semigroup" Test.Kore.Internal.MultiExists.test_Semigroup

    t652 <- testGroup "substitute" Test.Kore.Internal.TermLike.test_substitute

    t653 <- testGroup "refreshVariables" Test.Kore.Internal.TermLike.test_refreshVariables

    t654 <- testGroup "hasConstructorLikeTop" Test.Kore.Internal.TermLike.test_hasConstructorLikeTop

    t655 <- testGroup "renaming" Test.Kore.Internal.TermLike.test_renaming

    t656 <- testGroup "orientSubstitution" Test.Kore.Internal.TermLike.test_orientSubstitution

    t657 <- testGroup "toSyntaxPattern" Test.Kore.Internal.TermLike.test_toSyntaxPattern

    t658 <- testGroup "uninternalize" Test.Kore.Internal.TermLike.test_uninternalize

    t659 <- testGroup "expandedPattern" Test.Kore.Internal.Pattern.test_expandedPattern

    t660 <- testGroup "hasSimplifiedChildren" Test.Kore.Internal.Pattern.test_hasSimplifiedChildren

    t661 <- testGroup "toFromTermLike" Test.Kore.Internal.Pattern.test_toFromTermLike

    t662 <- testGroup "matchOverloading" Test.Kore.Simplify.Overloading.test_matchOverloading

    t663 <- testGroup "unifyOverloading" Test.Kore.Simplify.Overloading.test_unifyOverloading

    t664 <- testGroup "SubstitutionSimplifier" Test.Kore.Simplify.SubstitutionSimplifier.test_SubstitutionSimplifier

    t665 <- testGroup "simplificationIntegration" Test.Kore.Simplify.Integration.test_simplificationIntegration

    t666 <- testGroup "simplificationIntegrationUnification" Test.Kore.Simplify.Integration.test_simplificationIntegrationUnification

    t667 <- testGroup "substituteMap" Test.Kore.Simplify.Integration.test_substituteMap

    t668 <- testGroup "substituteList" Test.Kore.Simplify.Integration.test_substituteList

    t669 <- testGroup "substitute" Test.Kore.Simplify.Integration.test_substitute

    t670 <- testGroup "simplifySideCondition" Test.Kore.Simplify.Integration.test_simplifySideCondition

    t671 <- testGroup "anyBottom" Test.Kore.Simplify.Or.test_anyBottom

    t672 <- testGroup "deduplicateMiddle" Test.Kore.Simplify.Or.test_deduplicateMiddle

    t673 <- testGroup "simplify" Test.Kore.Simplify.Or.test_simplify

    t674 <- testGroup "valueProperties" Test.Kore.Simplify.Or.test_valueProperties

    t675 <- testGroup "simplify" Test.Kore.Simplify.DomainValue.test_simplify

    t676 <- testGroup "stringLiteralSimplification" Test.Kore.Simplify.StringLiteral.test_stringLiteralSimplification

    t677 <- testGroup "forallSimplification" Test.Kore.Simplify.Forall.test_forallSimplification

    t678 <- testGroup "topSimplification" Test.Kore.Simplify.Top.test_topSimplification

    t679 <- testGroup "equalsSimplification TermLike" Test.Kore.Simplify.Equals.test_equalsSimplification_TermLike

    t680 <- testGroup "equalsSimplification Or Pattern" Test.Kore.Simplify.Equals.test_equalsSimplification_Or_Pattern

    t681 <- testGroup "equalsSimplification Pattern" Test.Kore.Simplify.Equals.test_equalsSimplification_Pattern

    t682 <- testGroup "andTermsSimplification" Test.Kore.Simplify.AndTerms.test_andTermsSimplification

    t683 <- testGroup "equalsTermsSimplification" Test.Kore.Simplify.AndTerms.test_equalsTermsSimplification

    t684 <- testGroup "functionAnd" Test.Kore.Simplify.AndTerms.test_functionAnd

    t685 <- testGroup "simplify" Test.Kore.Simplify.InternalMap.test_simplify

    t686 <- testGroup "nextSimplification" Test.Kore.Simplify.Next.test_nextSimplification

    t687 <- testGroup "floorSimplification" Test.Kore.Simplify.Floor.test_floorSimplification

    t688 <- testGroup "andSimplification" Test.Kore.Simplify.And.test_andSimplification

    t689 <- testGroup "simplify" Test.Kore.Simplify.Inj.test_simplify

    t690 <- testGroup "simplifyEvaluated" Test.Kore.Simplify.Not.test_simplifyEvaluated

    t691 <- testGroup "orPatternSimplification" Test.Kore.Simplify.OrPattern.test_orPatternSimplification

    t692 <- testGroup "simplify" Test.Kore.Simplify.InternalSet.test_simplify

    t693 <- testGroup "simplify local functions" Test.Kore.Simplify.Condition.test_simplify_local_functions

    t694 <- testGroup "predicateSimplification" Test.Kore.Simplify.Condition.test_predicateSimplification

    t695 <- testGroup "simplifyPredicates" Test.Kore.Simplify.Condition.test_simplifyPredicates

    t696 <- testGroup "simplify" Test.Kore.Simplify.Predicate.test_simplify

    t697 <- testGroup "simplify SideCondition" Test.Kore.Simplify.Predicate.test_simplify_SideCondition

    t698 <- testGroup "extractFirstAssignment" Test.Kore.Simplify.Predicate.test_extractFirstAssignment

    t699 <- testGroup "simplifyEvaluated" Test.Kore.Simplify.Implies.test_simplifyEvaluated

    t700 <- testGroup "makeEvaluate" Test.Kore.Simplify.Exists.test_makeEvaluate

    t701 <- testGroup "simplify" Test.Kore.Simplify.Exists.test_simplify

    t702 <- testGroup "simplify" Test.Kore.Simplify.InternalList.test_simplify

    t703 <- testGroup "simplify sideConditionReplacements" Test.Kore.Simplify.TermLike.test_simplify_sideConditionReplacements

    t704 <- testGroup "simplifyOnly" Test.Kore.Simplify.TermLike.test_simplifyOnly

    t705 <- testGroup "ceilSimplification" Test.Kore.Simplify.Ceil.test_ceilSimplification

    t706 <- testGroup "applicationSimplification" Test.Kore.Simplify.Application.test_applicationSimplification

    t707 <- testGroup "simplify" Test.Kore.Simplify.Iff.test_simplify

    t708 <- testGroup "makeEvaluate" Test.Kore.Simplify.Iff.test_makeEvaluate

    -- t709 <- testGroup "simplifiesToSimplified" Test.Kore.Simplify.IntegrationProperty.test_simplifiesToSimplified

    t710 <- testGroup "regressionGeneratedTerms" Test.Kore.Simplify.IntegrationProperty.test_regressionGeneratedTerms

    t711 <- testGroup "bottomSimplification" Test.Kore.Simplify.Bottom.test_bottomSimplification

    t712 <- testGroup "Pattern simplify" Test.Kore.Simplify.Pattern.test_Pattern_simplify

    t713 <- testGroup "Pattern simplifyAndRemoveTopExists" Test.Kore.Simplify.Pattern.test_Pattern_simplifyAndRemoveTopExists

    t714 <- testGroup "Pattern simplify equalityterm" Test.Kore.Simplify.Pattern.test_Pattern_simplify_equalityterm

    t715 <- testGroup "matchInjs" Test.Kore.Simplify.InjSimplifier.test_matchInjs

    t716 <- testGroup "unifyInjs" Test.Kore.Simplify.InjSimplifier.test_unifyInjs

    t717 <- testGroup "normalize" Test.Kore.Simplify.InjSimplifier.test_normalize

    t718 <- testGroup "koreParser" Test.Kore.Parser.Parser.test_koreParser

    t719 <- testGroup "parseSortVariable" Test.Kore.Parser.Parser.test_parseSortVariable

    t720 <- testGroup "parseSort" Test.Kore.Parser.Parser.test_parseSort

    t721 <- testGroup "keyword" Test.Kore.Parser.Lexer.test_keyword

    t722 <- testGroup "colon" Test.Kore.Parser.Lexer.test_colon

    t723 <- testGroup "comma" Test.Kore.Parser.Lexer.test_comma

    t724 <- testGroup "bracesPair" Test.Kore.Parser.Lexer.test_bracesPair

    t725 <- testGroup "parseSymbolId" Test.Kore.Parser.Lexer.test_parseSymbolId

    t726 <- testGroup "braces" Test.Kore.Parser.Lexer.test_braces

    t727 <- testGroup "parens" Test.Kore.Parser.Lexer.test_parens

    t728 <- testGroup "brackets" Test.Kore.Parser.Lexer.test_brackets

    t729 <- testGroup "parseModuleName" Test.Kore.Parser.Lexer.test_parseModuleName

    t730 <- testGroup "parensTuple" Test.Kore.Parser.Lexer.test_parensTuple

    t731 <- testGroup "parseStringLiteral" Test.Kore.Parser.Lexer.test_parseStringLiteral

    t732 <- testGroup "space" Test.Kore.Parser.Lexer.test_space

    t733 <- testGroup "parseSExpr" Test.SMT.AST.test_parseSExpr

    pure $
        T.testGroup
            "test/Driver.hs"
            [ T.testGroup "meh" []
            , T.testGroup
                "Test"
                [ T.testGroup "meh" []
                , T.testGroup
                    "Data"
                    [ T.testGroup "meh" []
                    , T.testGroup "Graph.TopologicalSort" [t38]
                    , T.testGroup "InternedText" [t33, t34, t35, t36, t37]
                    , T.testGroup "Limit" [t29, t30, t31, t32]
                    , T.testGroup "Sup" [t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28]
                    ]
                , T.testGroup "Debug" [t8, t9, t10, t11]
                , T.testGroup "Injection" [t1, t2]
                , T.testGroup
                    "Kore"
                    [ T.testGroup "meh" []
                    , T.testGroup "AST.Common" [t82, t83]
                    , T.testGroup
                        "Attribute"
                        [ T.testGroup "meh" []
                        , T.testGroup "Assoc" [t523, t524, t525, t526, t527]
                        , T.testGroup
                            "Axiom"
                            [ T.testGroup "meh" []
                            , T.testGroup "Concrete" [t554, t555, t556, t557, t558, t559, t560, t561, t562, t563]
                            , T.testGroup "Symbolic" [t564, t565, t566, t567, t568, t569, t570, t571, t572, t573]
                            , T.testGroup "Unit" [t549, t550, t551, t552, t553]
                            ]
                        , T.testGroup "Comm" [t507, t508, t509, t510, t511]
                        , T.testGroup "Constructor" [t481, t482, t483, t484, t485]
                        , T.testGroup "Function" [t512, t513, t514, t515, t516]
                        , T.testGroup "Functional" [t447, t448, t449, t450, t451]
                        , T.testGroup "Hook" [t457, t458, t459, t460, t461, t462]
                        , T.testGroup "Idem" [t502, t503, t504, t505, t506]
                        , T.testGroup "Injective" [t492, t493, t494, t495, t496]
                        , T.testGroup "Label" [t463, t464, t465, t466, t467]
                        , T.testGroup "NonExecutable" [t497, t498, t499, t500, t501]
                        , T.testGroup "Overload" [t468, t469, t470, t471, t472, t473]
                        , T.testGroup "Owise" [t452, t453, t454, t455, t456]
                        , T.testGroup
                            "Pattern"
                            [ T.testGroup "meh" []
                            , T.testGroup "ConstructorLike" [t532]
                            , T.testGroup "Defined" [t534]
                            , T.testGroup "FreeVariables" [t528, t529, t530]
                            , T.testGroup "Function" [t535]
                            , T.testGroup "Functional" [t531]
                            , T.testGroup "Sort" [t533]
                            ]
                        , T.testGroup "Priority" [t517, t518, t519, t520, t521, t522]
                        , T.testGroup "ProductionID" [t417, t418, t419, t420, t421, t422]
                        , T.testGroup "Simplification" [t428, t429, t430, t431, t432, t433, t434, t435, t436]
                        , T.testGroup "Smtlib" [t478, t479, t480]
                        , T.testGroup
                            "Sort"
                            [ T.testGroup "meh" []
                            , T.testGroup "ConstructorsBuilder" [t536]
                            , T.testGroup "HasDomainValues" [t537, t538, t539, t540, t541, t542]
                            , T.testGroup "Unit" [t543, t544, t545, t546, t547, t548]
                            ]
                        , T.testGroup "SortInjection" [t442, t443, t444, t445, t446]
                        , T.testGroup "Subsort" [t474, t475, t476, t477]
                        , T.testGroup
                            "Symbol"
                            [ T.testGroup "meh" []
                            , T.testGroup "Anywhere" [t580, t581, t582, t583, t584]
                            , T.testGroup "Klabel" [t579]
                            , T.testGroup "Memo" [t585, t586, t587, t588, t589]
                            , T.testGroup "NoEvaluators" [t574, t575, t576, t577, t578]
                            , T.testGroup "SymbolKywd" [t590, t591, t592, t593, t594]
                            , t486
                            , t487
                            , t488
                            , t489
                            , t490
                            , t491
                            ]
                        , T.testGroup "Trusted" [t423, t424, t425, t426, t427]
                        , T.testGroup "UniqueId" [t437, t438, t439, t440, t441]
                        ]
                    , T.testGroup "BugReport" [t60, t61]
                    , T.testGroup
                        "Builtin"
                        [ T.testGroup "meh" []
                        , T.testGroup "AssocComm.CeilSimplifier" [t413, t414, t415, t416]
                        , T.testGroup "Bool" [t185, t186, t187, t188, t189, t190, t191, t192, t193, t194, t195, t196, t197, t198]
                        , T.testGroup "Encoding" [t248, t249]
                        , T.testGroup "Endianness" [t344, t345, t346]
                        , T.testGroup "Inj" [t231]
                        , T.testGroup "Int" [t347, t348, t349, t350, t351, t352, t353, t354, t355, t356, t357, t358, t359, t360, t361, t362, t363, t364, t365, t366, t367, t368, t369, t370, t371, t372, t373, t374, t375, t376, t377, t378, t379, t380, t381, t382, t383, t384, t385, t386, t387, t388, t389]
                        , T.testGroup "InternalBytes" [t212, t213, t214, t215, t216, t217, t218, t219, t220, t221, t222, t223, t224, t225, t226, t227, t228, t229, t230]
                        , T.testGroup "KEqual" [t390, t391, t392, t393, t394]
                        , T.testGroup "Krypto" [t202, t203, t204, t205, t206, t207, t208, t209, t210, t211]
                        , T.testGroup "List" [t395, t396, t397, t398, t399, t400, t401, t402, t403, t404, t405, t406, t407, t408, t409, t410, t411, t412]
                        , T.testGroup "Map" [t250, t251, t252, t253, t254, t255, t256, t257, t258, t259, t260, t261, t262, t263, t264, t265, t266, t267, t268, t269, t270, t271, t272, t273, t274, t275, t276, t277, t278, t279, t280, t281, t282, t283, t284, t285, t286, t287, t288, t289, t290, t291]
                        , T.testGroup "Set" [t292, t293, t294, t295, t296, t297, t298, t299, t300, t301, t302, t303, t304, t305, t306, t307, t308, t309, t310, t311, t312, t313, t314, t315, t316, t317, t318, t319, t320, t321, t322, t323, t324, t325, t326, t327, t328, t329, t330, t331, t332, t333, t334, t335, t336, t337, t338, t339, t340, t341, t342, t343]
                        , T.testGroup "Signedness" [t199, t200, t201]
                        , T.testGroup "String" [t232, t233, t234, t235, t236, t237, t238, t239, t240, t241, t242, t243, t244, t245, t246, t247]
                        , t55
                        , t56
                        ]
                    , T.testGroup
                        "Equation"
                        [ T.testGroup "meh" []
                        , T.testGroup "Application" [t69, t70]
                        , T.testGroup "Sentence" [t68]
                        , T.testGroup "Simplification" [t67]
                        ]
                    , T.testGroup "Error" [t59]
                    , T.testGroup "Exec" [t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54]
                    , T.testGroup
                        "IndexedModule"
                        [ T.testGroup "meh" []
                        , T.testGroup "Error" [t613]
                        , T.testGroup "OverloadGraph" [t604, t605, t606, t607]
                        , T.testGroup "Resolvers" [t608, t609]
                        , T.testGroup "SortGraph" [t610, t611, t612]
                        ]
                    , T.testGroup
                        "Internal"
                        [ T.testGroup "meh" []
                        , T.testGroup "ApplicationSorts" [t636]
                        , T.testGroup "From" [t635]
                        , T.testGroup "Key" [t646]
                        , T.testGroup "MultiAnd" [t633, t634]
                        , T.testGroup "MultiExists" [t649, t650, t651]
                        , T.testGroup "OrPattern" [t641, t642, t643, t644, t645]
                        , T.testGroup "Pattern" [t659, t660, t661]
                        , T.testGroup "Predicate" [t647, t648]
                        , T.testGroup "SideCondition" [t637, t638, t639, t640]
                        , T.testGroup "Substitution" [t629, t630, t631, t632]
                        , T.testGroup "TermLike" [t652, t653, t654, t655, t656, t657, t658]
                        ]
                    , T.testGroup
                        "Log"
                        [ T.testGroup "meh" []
                        , T.testGroup "DebugEvaluateCondition" [t79]
                        , T.testGroup "ErrorBottomTotalFunction" [t78]
                        , T.testGroup "WarnFunctionWithoutEvaluators" [t80]
                        , T.testGroup "WarnSymbolSMTRepresentation" [t81]
                        ]
                    , T.testGroup "Options" [t57, t58]
                    , T.testGroup
                        "Parser"
                        [ T.testGroup "meh" []
                        , T.testGroup "Lexer" [t721, t722, t723, t724, t725, t726, t727, t728, t729, t730, t731, t732]
                        , T.testGroup "Parser" [t718, t719, t720]
                        ]
                    , T.testGroup
                        "Reachability"
                        [ T.testGroup "meh" []
                        , T.testGroup "Claim" [t87, t88, t89, t100, t101, t102]
                        , T.testGroup "MockAllPath" [t94, t95, t96, t97, t98, t99]
                        , T.testGroup "OnePathStrategy" [t93]
                        , T.testGroup "Prove" [t90, t91]
                        , T.testGroup "SomeClaim" [t92]
                        ]
                    , T.testGroup
                        "Repl"
                        [ T.testGroup "meh" []
                        , T.testGroup "Graph" [t86]
                        , T.testGroup "Interpreter" [t84]
                        , T.testGroup "Parser" [t85]
                        ]
                    , T.testGroup
                        "Rewrite"
                        [ T.testGroup "meh" []
                        , T.testGroup "AntiLeft" [t126]
                        , T.testGroup
                            "Axiom"
                            [ T.testGroup "meh" []
                            , T.testGroup "EvaluationStrategy" [t166, t167, t168, t169, t170]
                            , T.testGroup "Identifier" [t171]
                            , T.testGroup "Matcher" [t149, t150, t151, t152, t153, t154, t155, t156, t157, t158, t159, t160, t161, t162, t163, t164]
                            , T.testGroup "Registry" [t165]
                            ]
                        , T.testGroup "ClaimPattern" [t131, t132]
                        , T.testGroup
                            "Function"
                            [ T.testGroup "meh" []
                            , T.testGroup "Evaluator" [t147]
                            , T.testGroup "Integration" [t139, t140, t141, t142, t143, t144, t145, t146]
                            , T.testGroup "Memo" [t148]
                            ]
                        , T.testGroup "Implication" [t133, t134, t135]
                        , T.testGroup "MockSymbols" [t106, t107]
                        , T.testGroup "Remainder" [t123]
                        , T.testGroup "RewriteStep" [t108, t109, t110, t111, t112, t113, t114]
                        , T.testGroup "RewritingVariable" [t124, t125]
                        , T.testGroup
                            "Rule"
                            [ T.testGroup "meh" []
                            , T.testGroup "Expand" [t138]
                            , T.testGroup "Simplify" [t136, t137]
                            , t103
                            , t104
                            , t105
                            ]
                        , T.testGroup "RulePattern" [t127, t128]
                        , T.testGroup
                            "SMT"
                            [ T.testGroup "meh" []
                            , T.testGroup "Evaluator" [t175, t176, t177, t178, t179, t180]
                            , T.testGroup
                                "Representation"
                                [ T.testGroup "meh" []
                                , T.testGroup "All" [t183]
                                , T.testGroup "Sorts" [t184]
                                , T.testGroup "Symbols" [t182]
                                ]
                            , T.testGroup "Sorts" [t181]
                            , T.testGroup "Symbols" [t173, t174]
                            , T.testGroup "Translate" [t172]
                            ]
                        , T.testGroup "Strategy" [t115, t116, t117, t118, t119, t120, t121, t122]
                        , T.testGroup "Transition" [t129, t130]
                        , t65
                        , t66
                        ]
                    , T.testGroup
                        "Simplify"
                        [ T.testGroup "meh" []
                        , T.testGroup "And" [t688]
                        , T.testGroup "AndTerms" [t682, t683, t684]
                        , T.testGroup "Application" [t706]
                        , T.testGroup "Bottom" [t711]
                        , T.testGroup "Ceil" [t705]
                        , T.testGroup "Condition" [t693, t694, t695]
                        , T.testGroup "DomainValue" [t675]
                        , T.testGroup "Equals" [t679, t680, t681]
                        , T.testGroup "Exists" [t700, t701]
                        , T.testGroup "Floor" [t687]
                        , T.testGroup "Forall" [t677]
                        , T.testGroup "Iff" [t707, t708]
                        , T.testGroup "Implies" [t699]
                        , T.testGroup "Inj" [t689]
                        , T.testGroup "InjSimplifier" [t715, t716, t717]
                        , T.testGroup "Integration" [t665, t666, t667, t668, t669, t670]
                        , T.testGroup "IntegrationProperty" [{- t709, -} t710]
                        , T.testGroup "InternalList" [t702]
                        , T.testGroup "InternalMap" [t685]
                        , T.testGroup "InternalSet" [t692]
                        , T.testGroup "Next" [t686]
                        , T.testGroup "Not" [t690]
                        , T.testGroup "Or" [t671, t672, t673, t674]
                        , T.testGroup "OrPattern" [t691]
                        , T.testGroup "Overloading" [t662, t663]
                        , T.testGroup "Pattern" [t712, t713, t714]
                        , T.testGroup "Predicate" [t696, t697, t698]
                        , T.testGroup "StringLiteral" [t676]
                        , T.testGroup "SubstitutionSimplifier" [t664]
                        , T.testGroup "TermLike" [t703, t704]
                        , T.testGroup "Top" [t678]
                        ]
                    , T.testGroup
                        "Syntax"
                        [ T.testGroup "meh" []
                        , T.testGroup "Id" [t595]
                        , T.testGroup
                            "Json"
                            [ T.testGroup "meh" []
                            , T.testGroup "Roundtrips" [t603]
                            , t600
                            , t601
                            , t602
                            ]
                        , T.testGroup "Variable" [t596, t597, t598, t599]
                        ]
                    , T.testGroup "TopBottom" [t39, t40]
                    , T.testGroup
                        "Unification"
                        [ T.testGroup "meh" []
                        , T.testGroup "SubstitutionNormalization" [t628]
                        , T.testGroup "Unifier" [t626, t627]
                        , T.testGroup "UnifierT" [t624, t625]
                        ]
                    , T.testGroup "Unparser" [t62, t63, t64]
                    , T.testGroup
                        "Validate.DefinitionVerifier"
                        [ T.testGroup "meh" []
                        , T.testGroup "Imports" [t75]
                        , T.testGroup "PatternVerifier" [t76, t77]
                        , T.testGroup "SentenceVerifier" [t72]
                        , T.testGroup "SortUsage" [t74]
                        , T.testGroup "UniqueNames" [t73]
                        , T.testGroup "UniqueSortVariables" [t71]
                        ]
                    , T.testGroup
                        "Variables"
                        [ T.testGroup "meh" []
                        , T.testGroup "Fresh" [t614, t615, t616, t617, t618]
                        , T.testGroup "Target" [t619, t620, t621, t622, t623]
                        ]
                    ]
                , T.testGroup "Pretty" [t0]
                , T.testGroup "SMT.AST" [t733]
                , T.testGroup "SQL" [t3, t4, t5, t6, t7]
                , T.testGroup "Stats" [t12]
                ]
            ]
ingredients :: [T.Ingredient]
ingredients = Test.Tasty.Runners.listingTests : Test.Tasty.Runners.Reporter.ingredient : T.defaultIngredients

main :: IO ()
main = do
    --    run all -- all
    --    run hangs -- known flaky property test
    --    run rest -- all the others
    run hanger

hanger, hangs, rest, all :: IO T.TestTree

-- | extracted test data, expected to hang all the time
hanger = testGroup "bye bye" Test.Kore.Simplify.IntegrationProperty.test_simplifier_hangs

-- | Hangs in ~10% of runs, consuming memory (slowly)
hangs = testGroup "simplifiesToSimplified" Test.Kore.Simplify.IntegrationProperty.test_simplifiesToSimplified

rest = tests
all = hangs >>= \h -> rest >>= \r -> testGroup "all" [h, r]

run :: IO T.TestTree -> IO ()
run ts = do
    E.setEnv "TERM" "dumb"
    args <- E.getArgs
    E.withArgs (["--hide-successes"] ++ args) $ ts >>= T.defaultMainWithIngredients ingredients
