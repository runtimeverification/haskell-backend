{- |
Module      : Kore.Builtin.KEqual
Description : Built-in KEQUAL operations
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
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
import Control.Monad qualified as Monad
import Data.HashMap.Strict qualified as HashMap
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin (
    UnifyEq (..),
    acceptAnySort,
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Error qualified
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
import Kore.Syntax.Definition (
    SentenceSymbol (..),
 )
import Kore.Unification.Unify as Unify
import Logic qualified
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

{- | @builtinFunctions@ defines the hooks for @KEQUAL.eq@, @KEQUAL.ne@, and
@KEQUAL.ite@.

@KEQUAL.eq@ and @KEQUAL.ne@ can take arbitrary terms (of the same sort) and
check whether they are equal or not, producing a builtin boolean value.

@KEQUAL.ite@ can take a boolean expression and two arbitrary terms (of the same
sort) and return the first term if the expression is true, and the second
otherwise.
-}
builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == eqKey = Just $ applicationAxiomSimplifier (evalKEq True)
    | key == neqKey = Just $ applicationAxiomSimplifier (evalKEq False)
    | key == iteKey = Just $ applicationAxiomSimplifier evalKIte
    | otherwise = Nothing

evalKEq ::
    forall variable.
    InternalVariable variable =>
    Bool ->
    SideCondition variable ->
    CofreeF
        (Application Symbol)
        (TermAttributes variable)
        (TermLike variable) ->
    Simplifier (AttemptedAxiom variable)
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
        MaybeT Simplifier (AttemptedAxiom variable)
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
    SideCondition RewritingVariableName ->
    CofreeF
        (Application Symbol)
        (TermAttributes RewritingVariableName)
        (TermLike RewritingVariableName) ->
    Simplifier (AttemptedAxiom RewritingVariableName)
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
neqKey = "KEQUAL.ne"

iteKey :: IsString s => s
iteKey = "KEQUAL.ite"

{- | Matches

@
\\equals{_, _}(eq(_,_), \\dv{Bool}(_))
@

and

@
\\and{_}(eq(_,_), \\dv{Bool}(_)),
@

symmetric in the two arguments.
-}
matchUnifyKequalsEq ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEq
matchUnifyKequalsEq = Builtin.matchUnifyEq eqKey
{-# INLINE matchUnifyKequalsEq #-}

-- | The @KEQUAL.ite@ hooked symbol applied to @term@-type arguments.
data IfThenElse term = IfThenElse
    { symbol :: !Symbol
    , condition :: !term
    , branch1, branch2 :: !term
    }

data UnifyIfThenElse = UnifyIfThenElse
    { ifThenElse :: IfThenElse (TermLike RewritingVariableName)
    , -- The term that was not matched by @matchIfThenElse@
      term :: TermLike RewritingVariableName
    }

{- | Matches

@
\\and{_}(ite(_,_,_), _)
@

symmetric in the two arguments.
-}
matchIfThenElse ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyIfThenElse
matchIfThenElse first second
    | Just ifThenElse <- matchITE first =
        Just $ UnifyIfThenElse{ifThenElse, term = second}
    | Just ifThenElse <- matchITE second =
        Just $ UnifyIfThenElse{ifThenElse, term = first}
    | otherwise = Nothing
  where
    matchITE (App_ symbol [condition, branch1, branch2]) = do
        hook' <- (getHook . symbolHook) symbol
        Monad.guard (hook' == iteKey)
        return IfThenElse{symbol, condition, branch1, branch2}
    matchITE _ = Nothing
{-# INLINE matchIfThenElse #-}

unifyIfThenElse ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    UnifyIfThenElse ->
    unifier (Pattern RewritingVariableName)
unifyIfThenElse unifyChildren unifyData =
    worker ifThenElse term
  where
    UnifyIfThenElse{ifThenElse, term} = unifyData
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
