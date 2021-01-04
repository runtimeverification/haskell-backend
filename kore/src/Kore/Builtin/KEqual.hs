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
    , unifyKequalsEq
    , unifyIfThenElse
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
import Kore.Builtin.EqTerm
import qualified Kore.Error
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeCeilPredicate_
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Definition
    ( SentenceSymbol (..)
    )
import Kore.Unification.Unify as Unify
import qualified Logic

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
builtinFunctions :: Map Text BuiltinAndAxiomSimplifier
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
    evaluate :: TermLike variable -> Maybe Bool
    evaluate = Bool.matchBool

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

{- | Match the @KEQUAL.eq@ hooked symbol.
 -}
matchKequalEq :: TermLike variable -> Maybe (EqTerm (TermLike variable))
matchKequalEq =
    matchEqTerm $ \symbol ->
        do
            hook2 <- (getHook . symbolHook) symbol
            Monad.guard (hook2 == eqKey)
        & isJust

unifyKequalsEq
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermSimplifier variable unifier
    -> NotSimplifier unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyKequalsEq unifyChildren notSimplifier a b =
    worker a b <|> worker b a
  where
    worker termLike1 termLike2
      | Just eqTerm <- matchKequalEq termLike1
      , isFunctionPattern termLike1
      = unifyEqTerm unifyChildren notSimplifier eqTerm termLike2
      | otherwise = empty

{- | The @KEQUAL.ite@ hooked symbol applied to @term@-type arguments.
 -}
data IfThenElse term =
    IfThenElse
        { symbol :: !Symbol
        , condition :: !term
        , branch1, branch2 :: !term
        }

{- | Match the @KEQUAL.eq@ hooked symbol.
 -}
matchIfThenElse :: TermLike variable -> Maybe (IfThenElse (TermLike variable))
matchIfThenElse (App_ symbol [condition, branch1, branch2]) = do
    hook' <- (getHook . symbolHook) symbol
    Monad.guard (hook' == iteKey)
    return IfThenElse { symbol, condition, branch1, branch2 }
matchIfThenElse _ = Nothing

unifyIfThenElse
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyIfThenElse unifyChildren a b =
    worker a b <|> worker b a
  where
    takeCondition value condition' =
        makeCeilPredicate_ (mkAnd (Bool.asInternal sort value) condition')
        & Condition.fromPredicate
      where
        sort = termLikeSort condition'
    worker termLike1 termLike2
      | Just ifThenElse <- matchIfThenElse termLike1
      = lift (takeBranch1 ifThenElse <|> takeBranch2 ifThenElse)
      where
        takeBranch1 IfThenElse { condition, branch1 } = do
            solution <- unifyChildren branch1 termLike2
            let branchCondition = takeCondition True condition
            Pattern.andCondition solution branchCondition
                & simplifyCondition SideCondition.top
                & Logic.lowerLogicT
        takeBranch2 IfThenElse { condition, branch2 } = do
            solution <- unifyChildren branch2 termLike2
            let branchCondition = takeCondition False condition
            Pattern.andCondition solution branchCondition
                & simplifyCondition SideCondition.top
                & Logic.lowerLogicT
    worker _ _ = empty
