module Test.Kore.ASTVerifier.DefinitionVerifier.SentenceVerifier (
    test_FreeVarInRHS,
) where

import Prelude.Kore

import Test.Tasty (
    TestTree,
 )

import qualified Control.Lens as Lens
import qualified Data.Default as Default
import Data.Generics.Product
import Kore.Attribute.Null (
    Null (..),
 )
import Kore.Builtin.External (
    externalize,
 )
import Kore.Error
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import Kore.Internal.TermLike (
    mkElemVar,
    mkSetVar,
    mkTop,
    weakExistsFinally,
 )
import Kore.Reachability (
    OnePathClaim (..),
 )
import Kore.Rewriting.RewritingVariable (
    ruleElementVariableFromId,
 )
import Kore.Step.AxiomPattern (
    AxiomPattern (..),
 )
import Kore.Step.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Syntax
import Kore.Syntax.Definition as Syntax

import Test.Kore (
    testId,
 )
import Test.Kore.ASTVerifier.DefinitionVerifier
import qualified Test.Kore.Step.MockSymbols as Mock

test_FreeVarInRHS :: [TestTree]
test_FreeVarInRHS =
    [ expectFailureWithError
        "Claim with free variable only in rhs"
        ( Error
            ["module 'MODULE'", "claim declaration"]
            "Found claim with universally-quantified variables\
            \ appearing only on the right-hand side"
        )
        ( simpleDefinitionFromSentences
            (ModuleName "MODULE")
            [ patternToSentence patternFreeVarInRHS
            , simpleSortSentence (SortName (getId Mock.testSortId))
            , sentenceAlias
            ]
        )
    , expectSuccess
        "Claim with only existentially quantified variables in rhs"
        ( simpleDefinitionFromSentences
            (ModuleName "MODULE")
            [ patternToSentence patternNoFreeVarInRHS
            , simpleSortSentence (SortName (getId Mock.testSortId))
            , sentenceAlias
            ]
        )
    ]
  where
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR
    x = mkSetVariable (testId "x") sortR
    sentenceAlias =
        sentenceAliasWithSortArgument
            (AliasName weakExistsFinally)
            sortR
            sortR
            [sortVariableR]
            (externalize $ mkSetVar x)
            & Lens.over
                (field @"sentenceAliasLeftPattern")
                (setField @"applicationChildren" [inject x])
            & asSentence

patternToSentence :: Pattern VariableName Null -> ParsedSentence
patternToSentence patt =
    SentenceClaimSentence $
        SentenceClaim $
            SentenceAxiom [] patt (Attributes [])

patternFreeVarInRHS :: Pattern VariableName Null
patternFreeVarInRHS =
    externalize . getAxiomPattern . from $
        OnePathClaim rulePatternFreeVarInRHS
  where
    rulePatternFreeVarInRHS :: ClaimPattern
    rulePatternFreeVarInRHS =
        ClaimPattern
            { left =
                Pattern.fromTermAndPredicate
                    (mkTop Mock.testSort)
                    makeTruePredicate
            , existentials = []
            , right =
                Pattern.fromTermAndPredicate
                    (mkElemVar (ruleElementVariableFromId "x" Mock.testSort))
                    makeTruePredicate
                    & OrPattern.fromPattern
            , attributes = Default.def
            }

patternNoFreeVarInRHS :: Pattern VariableName Null
patternNoFreeVarInRHS =
    externalize . getAxiomPattern . from $
        OnePathClaim rulePatternNoFreeVarInRHS
  where
    rulePatternNoFreeVarInRHS :: ClaimPattern
    rulePatternNoFreeVarInRHS =
        ClaimPattern
            { left =
                Pattern.fromTermAndPredicate
                    (mkTop Mock.testSort)
                    makeTruePredicate
            , existentials =
                [ruleElementVariableFromId "x" Mock.testSort]
            , right =
                Pattern.fromTermAndPredicate
                    (mkElemVar (ruleElementVariableFromId "x" Mock.testSort))
                    makeTruePredicate
                    & OrPattern.fromPattern
            , attributes = Default.def
            }
