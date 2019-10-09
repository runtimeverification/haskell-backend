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
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin
    ( acceptAnySort
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.And as And
import qualified Kore.Step.Simplification.Ceil as Ceil
import qualified Kore.Step.Simplification.Equals as Equals
import qualified Kore.Step.Simplification.Not as Not
import qualified Kore.Step.Simplification.Or as Or
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Definition
    ( SentenceSymbol (..)
    )

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( eqKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, acceptAnySort])
    , (neqKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, acceptAnySort])
    , (iteKey, iteVerifier)
    ]
  where
    iteVerifier :: Builtin.SymbolVerifier
    iteVerifier = Builtin.SymbolVerifier $ \findSort decl -> do
        let SentenceSymbol { sentenceSymbolSorts = sorts } = decl
            SentenceSymbol { sentenceSymbolResultSort = result } = decl
            arity = length sorts
        Kore.Error.withContext "In argument sorts" $
            case sorts of
                [firstSort, secondSort, thirdSort] -> do
                    Builtin.runSortVerifier Bool.assertSort findSort firstSort
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
    [ (eqKey, applicationAxiomSimplifier (evalKEq True))
    , (neqKey, applicationAxiomSimplifier (evalKEq False))
    , (iteKey, applicationAxiomSimplifier evalKIte)
    ]

evalKEq
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Bool
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> CofreeF
        (Application Symbol)
        (Attribute.Pattern variable)
        (TermLike variable)
    -> simplifier (AttemptedAxiom variable)
evalKEq true _ _ (valid :< app) =
    case applicationChildren of
        [t1, t2] -> evalEq t1 t2
        _ -> Builtin.wrongArity (if true then eqKey else neqKey)
  where
    false = not true
    sort = Attribute.patternSort valid
    Application { applicationChildren } = app
    evalEq termLike1 termLike2 = do
        let pattern1 = Pattern.fromTermLike termLike1
            pattern2 = Pattern.fromTermLike termLike2

        defined1 <- Ceil.makeEvaluate Predicate.topTODO pattern1
        defined2 <- Ceil.makeEvaluate Predicate.topTODO pattern2
        defined <- And.simplifyEvaluated defined1 defined2

        equalTerms <-
            Equals.makeEvaluateTermsToPredicate
                termLike1
                termLike2
                Predicate.topTODO
        let trueTerm = Bool.asInternal sort true
            truePatterns = Pattern.withCondition trueTerm <$> equalTerms

        notEqualTerms <- Not.simplifyEvaluatedPredicate equalTerms
        let falseTerm = Bool.asInternal sort false
            falsePatterns = Pattern.withCondition falseTerm <$> notEqualTerms

        let undefinedResults = Or.simplifyEvaluated truePatterns falsePatterns
        results <- And.simplifyEvaluated defined undefinedResults
        pure $ Applied AttemptedAxiomResults
            { results
            , remainders = OrPattern.bottom
            }

evalKIte
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> CofreeF
        (Application Symbol)
        (Attribute.Pattern variable)
        (TermLike variable)
    -> simplifier (AttemptedAxiom variable)
evalKIte _ _ (_ :< app) =
    case app of
        Application { applicationChildren = [expr, t1, t2] } ->
            evalIte expr t1 t2
        _ -> Builtin.wrongArity iteKey
  where
    evaluate
        :: TermLike variable
        -> Maybe Bool
    evaluate (Recursive.project -> _ :< pat) =
        case pat of
            BuiltinF dv ->
                Just (Bool.extractBoolDomainValue iteKey dv)
            _ -> Nothing

    evalIte expr t1 t2 =
        case evaluate expr of
            Just result
                | result    -> purePatternAxiomEvaluator t1
                | otherwise -> purePatternAxiomEvaluator t2
            Nothing    -> notApplicableAxiomEvaluator

eqKey :: IsString s => s
eqKey = "KEQUAL.eq"

neqKey :: IsString s => s
neqKey = "KEQUAL.neq"

iteKey :: IsString s => s
iteKey = "KEQUAL.ite"
