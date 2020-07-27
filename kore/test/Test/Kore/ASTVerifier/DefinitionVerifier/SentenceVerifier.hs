module Test.Kore.ASTVerifier.DefinitionVerifier.SentenceVerifier
    ( test_FreeVarInRHS
    ) where

import Prelude.Kore

import Test.Tasty
    ( TestTree
    )

import qualified Control.Lens as Lens
import qualified Data.Default as Default
import Data.Generics.Product
import Kore.Attribute.Null
    ( Null (..)
    )
import Kore.Builtin.External
    ( externalize
    )
import Kore.Error
import Kore.Internal.Predicate
import Kore.Internal.TermLike
    ( mkElemVar
    , mkSetVar
    , mkTop
    , mkTop
    )
import qualified Kore.Step.Rule as Rule
import Kore.Step.RulePattern
    ( OnePathRule (..)
    , RHS (..)
    , RulePattern (..)
    , weakExistsFinally
    )
import Kore.Syntax
import Kore.Syntax.Definition as Syntax

import Test.Kore
    ( testId
    )
import Test.Kore.ASTVerifier.DefinitionVerifier
import qualified Test.Kore.Step.MockSymbols as Mock

test_FreeVarInRHS :: [TestTree]
test_FreeVarInRHS =
    [ expectFailureWithError "Claim with free variable only in rhs"
        (Error
            ["module 'MODULE'" ,"claim declaration"]
            "Found claim with universally-quantified variables\
            \ appearing only on the right-hand side"
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ patternToSentence patternFreeVarInRHS
            , simpleSortSentence (SortName (getId Mock.testSortId))
            , sentenceAlias
            ]
        )
    , expectSuccess "Claim with only existentially quantified variables in rhs"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
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
        & Lens.over (field @"sentenceAliasLeftPattern")
            (setField @"applicationChildren" [inject x])
        & asSentence

patternToSentence :: Pattern VariableName Null -> ParsedSentence
patternToSentence patt =
    SentenceClaimSentence $ SentenceClaim
    $ SentenceAxiom [] patt (Attributes [])

patternFreeVarInRHS :: Pattern VariableName Null
patternFreeVarInRHS =
    externalize
    $ Rule.axiomPatternToTerm $ Rule.OnePathClaimPattern
    $ OnePathRule rulePatternFreeVarInRHS
  where
    rulePatternFreeVarInRHS :: RulePattern VariableName
    rulePatternFreeVarInRHS = RulePattern
        { left = mkTop Mock.testSort
        , antiLeft = Nothing
        , requires = makeTruePredicate Mock.testSort
        , rhs =
            RHS
                { existentials = []
                , right = mkElemVar (mkElementVariable "x" Mock.testSort)
                , ensures = makeTruePredicate Mock.testSort
                }
        , attributes = Default.def
        }

patternNoFreeVarInRHS :: Pattern VariableName Null
patternNoFreeVarInRHS =
    externalize
    $ Rule.axiomPatternToTerm $ Rule.OnePathClaimPattern
    $ OnePathRule rulePatternNoFreeVarInRHS
  where
    rulePatternNoFreeVarInRHS :: RulePattern VariableName
    rulePatternNoFreeVarInRHS = RulePattern
        { left = mkTop Mock.testSort
        , antiLeft = Nothing
        , requires = makeTruePredicate Mock.testSort
        , rhs =
            RHS
                { existentials = [mkElementVariable "x" Mock.testSort]
                , right = mkElemVar (mkElementVariable "x" Mock.testSort)
                , ensures = makeTruePredicate Mock.testSort
                }
        , attributes = Default.def
        }
