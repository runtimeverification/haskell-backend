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
    ( verifiers
    , builtinFunctions
    , KEqual (..)
    , termKEquals
      -- * keys
    , eqKey
    , neqKey
    , iteKey
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    , hoistMaybe
    )
import qualified Control.Monad as Monad
import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )

import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin
    ( acceptAnySort
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeEqualsPredicate_
    , makeNotPredicate
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Definition
    ( SentenceSymbol (..)
    )
import Kore.Unification.Unify
    ( MonadUnify
    )

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = mempty
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

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
    :: forall variable simplifier
    .  (InternalVariable variable, MonadSimplify simplifier)
    => Bool
    -> CofreeF
        (Application Symbol)
        (Attribute.Pattern variable)
        (TermLike variable)
    -> simplifier (AttemptedAxiom variable)
evalKEq true (valid :< app) =
    case applicationChildren of
        [t1, t2] -> Builtin.getAttemptedAxiom (evalEq t1 t2)
        _ -> Builtin.wrongArity (if true then eqKey else neqKey)
  where
    sort = Attribute.patternSort valid
    Application { applicationChildren } = app
    comparison x y
        | true = x == y
        | otherwise = x /= y
    evalEq
        :: TermLike variable
        -> TermLike variable
        -> MaybeT simplifier (AttemptedAxiom variable)
    evalEq termLike1 termLike2 = do
        asConcrete1 <- hoistMaybe $ Builtin.toKey termLike1
        asConcrete2 <- hoistMaybe $ Builtin.toKey termLike2
        Builtin.appliedFunction
            $ Bool.asPattern sort
            $ comparison asConcrete1 asConcrete2

evalKIte
    :: forall variable simplifier
    .  (InternalVariable variable, MonadSimplify simplifier)
    => CofreeF
        (Application Symbol)
        (Attribute.Pattern variable)
        (TermLike variable)
    -> simplifier (AttemptedAxiom variable)
evalKIte (_ :< app) =
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

{- | The @KEQUAL.eq@ hooked symbol applied to @term@-type arguments.
 -}
data KEqual term =
    KEqual
        { symbol :: !Symbol
        , operand1, operand2 :: !term
        }

{- | Match the @KEQUAL.eq@ hooked symbol.
 -}
matchKEqual :: TermLike variable -> Maybe (KEqual (TermLike variable))
matchKEqual (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == eqKey)
    return KEqual { symbol, operand1, operand2 }
matchKEqual _ = Nothing

termKEquals
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termKEquals unifyChildren a b =
    worker a b <|> worker b a
  where
    unifyChildren' term1 term2 =
        unificationPredicate term1 term2
        <|> return (makeEqualsPredicate_ term1 term2)
    unificationPredicate term1 term2 =
        Condition.toPredicate
        . Pattern.withoutTerm
        <$> unifyChildren term1 term2
    atLeastOneSymbolic term1 term2 =
        case (Builtin.toKey term1, Builtin.toKey term2) of
           (Nothing, _) -> True
           (_, Nothing) -> True
           _ -> False
    worker termLike1 termLike2
      | Just KEqual { operand1, operand2 } <- matchKEqual termLike1
      , isFunctionPattern termLike1
      , Just value2 <- Bool.matchBool termLike2
      , value2
      , atLeastOneSymbolic operand1 operand2
      = lift $ do
        condition <- unifyChildren' operand1 operand2
        pure Conditional
            { term = termLike2
            , predicate = condition
            , substitution = mempty
            }
      | Just KEqual { operand1, operand2 } <- matchKEqual termLike1
      , isFunctionPattern termLike1
      , Just value2 <- Bool.matchBool termLike2
      , not value2
      , atLeastOneSymbolic operand1 operand2
      = lift $ do
        condition <- unifyChildren' operand1 operand2
        pure Conditional
            { term = termLike2
            , predicate = makeNotPredicate condition
            , substitution = mempty
            }
    worker _ _ = empty
