{- |
Module      : Kore.Builtin.KEqual
Description : Built-in KEQUAL operations
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.KEqual as KEqual
@
 -}
module Kore.Builtin.KEqual
    ( symbolVerifiers
    , builtinFunctions
      -- * keys
    , eqKey
    , neqKey
    , iteKey
    ) where

import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )

import           Kore.AST.Pure
import           Kore.AST.Sentence
                 ( SentenceSymbol (..) )
import           Kore.AST.Valid
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..), AttemptedFunction (..),
                 notApplicableFunctionEvaluator, purePatternFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier )
import           Kore.Step.Simplification.Equals
                 ( makeEvaluate )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( eqKey
      , Builtin.verifySymbol Bool.assertSort [trivialVerifier, trivialVerifier])
    , (neqKey
      , Builtin.verifySymbol Bool.assertSort [trivialVerifier, trivialVerifier])
    , (iteKey, iteVerifier)
    ]
  where
    trivialVerifier :: Builtin.SortVerifier
    trivialVerifier = const $ const $ Right ()

    iteVerifier :: Builtin.SymbolVerifier
    iteVerifier
        findSort
        SentenceSymbol
            { sentenceSymbolSorts = sorts
            , sentenceSymbolResultSort = result
            }
      =
        Kore.Error.withContext "In argument sorts" $
            case sorts of
                [firstSort, secondSort, thirdSort] -> do
                    Bool.assertSort findSort firstSort
                    Kore.Error.koreFailWhen
                        (secondSort /= thirdSort)
                        "Expected continuations to match"
                    Kore.Error.koreFailWhen
                        (secondSort /= result)
                        "Expected continuations to match"
                    return ()
                _ ->
                    Kore.Error.koreFail
                        ( "Wrong arity, expected 3 but got "
                        ++ show arity ++ " in KEQUAL.ite"
                        )
      where
        arity = length sorts

{- | @builtinFunctions@ defines the hooks for @KEQUAL.eq@, @KEQUAL.neq@, and
@KEQUAL.ite@.

@KEQUAL.eq@ and @KEQUAL.neq@ can take arbitrary terms (of the same sort) and
check whether they are equal or not, producing a builtin boolean value.

@KEQUAL.ite@ can take a boolean expression and two arbitrary terms (of the same
sort) and return the first term if the expression is true, and the second
otherwise.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
    [ (eqKey, ApplicationFunctionEvaluator (evalKEq True))
    , (neqKey, ApplicationFunctionEvaluator (evalKEq False))
    , (iteKey, ApplicationFunctionEvaluator evalKIte)
    ]

evalKEq
    ::  ( FreshVariable variable
        , OrdMetaOrObject variable
        , SortedVariable variable
        , ShowMetaOrObject variable
        , Unparse (variable Object)
        )
    => Bool
    -> MetadataTools.MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object Simplifier
    -> StepPatternSimplifier Object variable
    -> CofreeF
        (Application Object)
        (Valid (variable Object) Object)
        (StepPattern Object variable)
    -> Simplifier
        ( AttemptedFunction Object variable
        , SimplificationProof Object
        )
evalKEq true tools substitutionSimplifier _ (valid :< app) =
    case applicationChildren of
        [t1, t2] -> evalEq t1 t2
        _ -> Builtin.wrongArity (if true then eqKey else neqKey)
  where
    false = not true
    Valid { patternSort } = valid
    Application { applicationChildren } = app
    evalEq t1 t2 = do
        (result, _proof) <- makeEvaluate tools substitutionSimplifier ep1 ep2
        case () of
            _ | OrOfExpandedPattern.isTrue result ->
                purePatternFunctionEvaluator (Bool.asPattern patternSort true)
              | OrOfExpandedPattern.isFalse result ->
                purePatternFunctionEvaluator (Bool.asPattern patternSort false)
              | otherwise -> notApplicableFunctionEvaluator
      where
        ep1 = ExpandedPattern.fromPurePattern t1
        ep2 = ExpandedPattern.fromPurePattern t2

evalKIte
    ::  forall variable
    .   ( FreshVariable variable
        , OrdMetaOrObject variable
        , SortedVariable variable
        , ShowMetaOrObject variable
        )
    => MetadataTools.MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object Simplifier
    -> StepPatternSimplifier Object variable
    -> CofreeF
        (Application Object)
        (Valid (variable Object) Object)
        (StepPattern Object variable)
    -> Simplifier
        ( AttemptedFunction Object variable
        , SimplificationProof Object
        )
evalKIte _ _ _ (_ :< app) =
    case app of
        Application { applicationChildren = [expr, t1, t2] } ->
            evalIte expr t1 t2
        _ -> Builtin.wrongArity iteKey
  where
    evaluate
        :: StepPattern Object variable
        -> Maybe Bool
    evaluate (Recursive.project -> _ :< pat) =
        case pat of
            DomainValuePattern dv -> Just (get dv)
            _ -> Nothing

    get :: DomainValue Object Domain.Builtin child -> Bool
    get =
        Builtin.runParser iteKey
        . Builtin.parseDomainValue Bool.parse

    evalIte expr t1 t2 =
        case evaluate expr of
            Just result
                | result    -> purePatternFunctionEvaluator t1
                | otherwise -> purePatternFunctionEvaluator t2
            Nothing    -> notApplicableFunctionEvaluator

eqKey :: IsString s => s
eqKey = "KEQUAL.eq"

neqKey :: IsString s => s
neqKey = "KEQUAL.neq"

iteKey :: IsString s => s
iteKey = "KEQUAL.ite"
