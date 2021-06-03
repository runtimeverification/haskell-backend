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
module Kore.Builtin.KEqual (
    verifiers,
    builtinFunctions,
    unifyKequalsEq,
    unifyIfThenElse,
    matchUnifyKequalsEq,
    matchIfThenElse,

    -- * keys
    eqKey,
    neqKey,
    iteKey,
) where

import Control.Error (
    MaybeT,
 )
import qualified Control.Monad as Monad
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin (
    acceptAnySort,
 )
import qualified Kore.Builtin.Builtin as Builtin
import Kore.Builtin.EqTerm
import qualified Kore.Error
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Definition (
    SentenceSymbol (..),
 )
import Kore.Unification.Unify as Unify
import qualified Logic
import Prelude.Kore

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
        [
            ( eqKey
            , Builtin.verifySymbol Bool.assertSort [acceptAnySort, acceptAnySort]
            )
        ,
            ( neqKey
            , Builtin.verifySymbol Bool.assertSort [acceptAnySort, acceptAnySort]
            )
        , (iteKey, iteVerifier)
        ]
  where
    iteVerifier :: Builtin.SymbolVerifier
    iteVerifier = Builtin.SymbolVerifier $ \findSort decl -> do
        let SentenceSymbol{sentenceSymbolSorts = sorts} = decl
            SentenceSymbol{sentenceSymbolResultSort = result} = decl
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
                            ++ show arity
                            ++ " in KEQUAL.ite"
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

evalKEq ::
    forall variable simplifier.
    (InternalVariable variable, MonadSimplify simplifier) =>
    Bool ->
    SideCondition variable ->
    CofreeF
        (Application Symbol)
        (TermAttributes variable)
        (TermLike variable) ->
    simplifier (AttemptedAxiom variable)
evalKEq true _ (valid :< app) =
    case applicationChildren of
        [t1, t2] -> Builtin.getAttemptedAxiom (evalEq t1 t2)
        _ -> Builtin.wrongArity (if true then eqKey else neqKey)
  where
    sort = termSort valid
    Application{applicationChildren} = app
    evalEq ::
        TermLike variable ->
        TermLike variable ->
        MaybeT simplifier (AttemptedAxiom variable)
    evalEq termLike1 termLike2
        | termLike1 == termLike2 =
            Builtin.appliedFunction $ Bool.asPattern sort true
        | otherwise = do
            -- Here we handle the case when both patterns are constructor-like
            -- (so that equality is syntactic). If either pattern is not
            -- constructor-like, we postpone evaluation until we know more.
            Monad.guard (TermLike.isConstructorLike termLike1)
            Monad.guard (TermLike.isConstructorLike termLike2)
            Builtin.appliedFunction $ Bool.asPattern sort (not true)

evalKIte ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    CofreeF
        (Application Symbol)
        (TermAttributes RewritingVariableName)
        (TermLike RewritingVariableName) ->
    simplifier (AttemptedAxiom RewritingVariableName)
evalKIte _ (_ :< app) =
    case app of
        Application{applicationChildren = [expr, t1, t2]} ->
            evalIte expr t1 t2
        _ -> Builtin.wrongArity iteKey
  where
    evaluate :: TermLike RewritingVariableName -> Maybe Bool
    evaluate = Bool.matchBool

    evalIte expr t1 t2 =
        case evaluate expr of
            Just result
                | result -> purePatternAxiomEvaluator t1
                | otherwise -> purePatternAxiomEvaluator t2
            Nothing -> notApplicableAxiomEvaluator

eqKey :: IsString s => s
eqKey = "KEQUAL.eq"

neqKey :: IsString s => s
neqKey = "KEQUAL.neq"

iteKey :: IsString s => s
iteKey = "KEQUAL.ite"

-- | Match the @KEQUAL.eq@ hooked symbol.
matchKequalEq :: TermLike variable -> Maybe (EqTerm (TermLike variable))
matchKequalEq =
    matchEqTerm $ \symbol ->
        do
            hook2 <- (getHook . symbolHook) symbol
            Monad.guard (hook2 == eqKey)
            & isJust

data UnifyKequalsEq = UnifyKequalsEq
    { eqTerm :: !(EqTerm (TermLike RewritingVariableName))
    , value :: !Bool
    }

{- | Matches

@
\\equals{_, _}(eq(_,_), \\dv{Bool}(_))
@

and

@
\\and{_}(eq(_,_), \\dv{Bool}(_))
@
-}
matchUnifyKequalsEq ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyKequalsEq
matchUnifyKequalsEq first second
    | Just eqTerm <- matchKequalEq first
      , isFunctionPattern first
      , Just value <- Bool.matchBool second =
        Just UnifyKequalsEq{eqTerm, value}
    | otherwise = Nothing
{-# INLINE matchUnifyKequalsEq #-}

unifyKequalsEq ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    NotSimplifier unifier ->
    UnifyKequalsEq ->
    unifier (Pattern RewritingVariableName)
unifyKequalsEq unifyChildren (NotSimplifier notSimplifier) unifyData =
    do
        solution <- unifyChildren operand1 operand2 & OrPattern.gather
        let solution' = MultiOr.map eraseTerm solution
        (if value then pure else notSimplifier SideCondition.top) solution'
            >>= Unify.scatter
  where
    UnifyKequalsEq{eqTerm, value} = unifyData
    EqTerm{operand1, operand2} = eqTerm
    eraseTerm = Pattern.fromCondition_ . Pattern.withoutTerm

-- | The @KEQUAL.ite@ hooked symbol applied to @term@-type arguments.
data IfThenElse term = IfThenElse
    { symbol :: !Symbol
    , condition :: !term
    , branch1, branch2 :: !term
    }

-- | Match the @KEQUAL.eq@ hooked symbol.
matchIfThenElse :: TermLike variable -> Maybe (IfThenElse (TermLike variable))
matchIfThenElse (App_ symbol [condition, branch1, branch2]) = do
    hook' <- (getHook . symbolHook) symbol
    Monad.guard (hook' == iteKey)
    return IfThenElse{symbol, condition, branch1, branch2}
matchIfThenElse _ = Nothing
{-# INLINE matchIfThenElse #-}

unifyIfThenElse ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    IfThenElse (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName ->
    unifier (Pattern RewritingVariableName)
unifyIfThenElse unifyChildren ifThenElse second =
    worker ifThenElse second
  where
    takeCondition value condition' =
        makeCeilPredicate (mkAnd (Bool.asInternal sort value) condition')
            & Condition.fromPredicate
      where
        sort = termLikeSort condition'
    worker ifThenElse' second' =
        takeBranch1 ifThenElse' <|> takeBranch2 ifThenElse'
      where
        takeBranch1 IfThenElse{condition, branch1} = do
            solution <- unifyChildren branch1 second'
            let branchCondition = takeCondition True condition
            Pattern.andCondition solution branchCondition
                & simplifyCondition SideCondition.top
                & Logic.lowerLogicT
        takeBranch2 IfThenElse{condition, branch2} = do
            solution <- unifyChildren branch2 second'
            let branchCondition = takeCondition False condition
            Pattern.andCondition solution branchCondition
                & simplifyCondition SideCondition.top
                & Logic.lowerLogicT
