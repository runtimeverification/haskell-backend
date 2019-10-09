{-|
Module      : Kore.Step.SMT.Translate
Description : Translates conditions to something that a SMT solver understands.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.SMT.Translate
    ( translatePredicate
    , Translator
    , VarContext
    , evalTranslator
    , runTranslator
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( MaybeT
    , hoistMaybe
    )
import Control.Monad.Counter
    ( CounterT
    , evalCounterT
    )
import Control.Monad.Except
import Control.Monad.Morph as Morph
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Reflection

import Kore.Attribute.Hook
import Kore.Attribute.Smtlib
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import Kore.IndexedModule.MetadataTools
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
import Kore.Step.SMT.Resolvers
    ( translateSort
    , translateSymbol
    )
import Kore.Unparser
import SMT
    ( SExpr (..)
    )
import qualified SMT

-- ----------------------------------------------------------------
-- Predicate translation

{- | Translate a predicate for SMT.

The predicate may inhabit an arbitrary sort. Logical connectives are translated
to their SMT counterparts. Quantifiers, @\\ceil@, @\\floor@, and @\\in@ are
uninterpreted (translated as variables) as is @\\equals@ if its arguments are
not builtins or predicates. All other patterns are not translated and prevent
the predicate from being sent to SMT.

 -}
translatePredicate
    :: forall p variable m .
        ( Ord variable
        , Unparse variable
        , Given (SmtMetadataTools Attribute.Symbol)
        , p ~ TermLike variable
        , Monad m
        )
    => (SExpr -> p -> Translator m p SExpr)
    -> Predicate variable
    -> Translator m p SExpr
translatePredicate translateUninterpreted predicate =
    translatePredicatePattern $ unwrapPredicate predicate
  where
    translatePredicatePattern
        :: TermLike variable
        -> Translator m (TermLike variable) SExpr
    translatePredicatePattern pat =
        case Cofree.tailF (Recursive.project pat) of
            EvaluatedF child -> translatePredicatePattern (getEvaluated child)
            -- Logical connectives: translate as connectives
            AndF and' -> translatePredicateAnd and'
            BottomF _ -> return (SMT.bool False)
            EqualsF eq ->
                -- Equality of predicates and builtins can be translated to
                -- equality in the SMT solver, but other patterns must remain
                -- uninterpreted.
                    translatePredicateEquals eq
                <|> translateUninterpreted SMT.tBool pat
            IffF iff -> translatePredicateIff iff
            ImpliesF implies -> translatePredicateImplies implies
            NotF not' -> translatePredicateNot not'
            OrF or' -> translatePredicateOr or'
            TopF _ -> return (SMT.bool True)

            -- Uninterpreted: translate as variables
            CeilF _ -> translateUninterpreted SMT.tBool pat
            ExistsF _ -> translateUninterpreted SMT.tBool pat
            FloorF _ -> translateUninterpreted SMT.tBool pat
            ForallF _ -> translateUninterpreted SMT.tBool pat
            InF _ -> translateUninterpreted SMT.tBool pat

            -- Invalid: no translation, should not occur in predicates
            MuF _ -> empty
            NuF _ -> empty
            ApplySymbolF _ -> empty
            ApplyAliasF _ -> empty
            BuiltinF _ -> empty
            DomainValueF _ -> empty
            NextF _ -> empty
            RewritesF _ -> empty
            VariableF _ -> empty
            StringLiteralF _ -> empty
            InhabitantF _ -> empty

    translatePredicateAnd And { andFirst, andSecond } =
        SMT.and
            <$> translatePredicatePattern andFirst
            <*> translatePredicatePattern andSecond

    translatePredicateEquals
        Equals
            { equalsOperandSort
            , equalsFirst
            , equalsSecond
            }
      =
        SMT.eq
            <$> translatePredicateEqualsChild equalsFirst
            <*> translatePredicateEqualsChild equalsSecond
      where
        translatePredicateEqualsChild child =
            -- Attempt to translate patterns in builtin sorts, or failing that,
            -- as predicates.
            (<|>)
                (translatePattern equalsOperandSort child)
                (translatePredicatePattern child)

    translatePredicateIff Iff { iffFirst, iffSecond } =
        iff
            <$> translatePredicatePattern iffFirst
            <*> translatePredicatePattern iffSecond
      where
        iff a b = SMT.and (SMT.implies a b) (SMT.implies b a)

    translatePredicateImplies Implies { impliesFirst, impliesSecond } =
        SMT.implies
            <$> translatePredicatePattern impliesFirst
            <*> translatePredicatePattern impliesSecond

    translatePredicateNot Not { notChild } =
        SMT.not <$> translatePredicatePattern notChild

    translatePredicateOr Or { orFirst, orSecond } =
        SMT.or
            <$> translatePredicatePattern orFirst
            <*> translatePredicatePattern orSecond

    -- | Translate a functional pattern in the builtin Int sort for SMT.
    translateInt
        ::  ( Given (SmtMetadataTools Attribute.Symbol)
            , Ord variable
            , p ~ TermLike variable
            )
        => p
        -> Translator m p SExpr
    translateInt pat =
        case Cofree.tailF (Recursive.project pat) of
            VariableF _ -> translateUninterpreted SMT.tInt pat
            BuiltinF dv ->
                return $ SMT.int $ Builtin.Int.extractIntDomainValue
                    "while translating dv to SMT.int" dv
            ApplySymbolF app ->
                (<|>)
                    (translateApplication app)
                    (translateUninterpreted SMT.tInt pat)
            _ -> empty

    -- | Translate a functional pattern in the builtin Bool sort for SMT.
    translateBool
        ::  ( Given (SmtMetadataTools Attribute.Symbol)
            , Ord variable
            , p ~ TermLike variable
            )
        => p
        -> Translator m p SExpr
    translateBool pat =
        case Cofree.tailF (Recursive.project pat) of
            VariableF _ -> translateUninterpreted SMT.tBool pat
            BuiltinF dv ->
                return $ SMT.bool $ Builtin.Bool.extractBoolDomainValue
                    "while translating dv to SMT.bool" dv
            NotF Not { notChild } ->
                -- \not is equivalent to BOOL.not for functional patterns.
                -- The following is safe because non-functional patterns
                -- will fail to translate.
                SMT.not <$> translateBool notChild
            ApplySymbolF app ->
                (<|>)
                    (translateApplication app)
                    (translateUninterpreted SMT.tBool pat)
            _ -> empty

    translateApplication
        ::  ( Given (SmtMetadataTools Attribute.Symbol)
            , Ord variable
            , p ~ TermLike variable
            )
        => Application Symbol p
        -> Translator m p SExpr
    translateApplication
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
      = do
        sexpr <- case translateSymbol applicationSymbolOrAlias of
            Nothing -> empty  -- The symbol was not declared, give up.
            Just sexpr -> return sexpr
        children <- zipWithM translatePattern
            applicationChildrenSorts
            applicationChildren
        return $ shortenSExpr (applySExpr sexpr children)
      where
        applicationChildrenSorts = termLikeSort <$> applicationChildren

    translatePattern
        ::  ( Given (SmtMetadataTools Attribute.Symbol)
            , p ~ TermLike variable
            )
        => Sort
        -> p
        -> Translator m p SExpr
    translatePattern sort pat =
        case getHook of
            Just builtinSort
              | builtinSort == Builtin.Bool.sort -> translateBool pat
              | builtinSort == Builtin.Int.sort -> translateInt pat
            _ -> case Cofree.tailF $ Recursive.project pat of
                    VariableF _ -> do
                        smtSort <- hoistMaybe $ translateSort sort
                        translateUninterpreted smtSort pat
                    ApplySymbolF app -> translateApplication app
                    _ -> empty
      where
        tools :: SmtMetadataTools Attribute.Symbol
        tools = given
        Attribute.Sort { hook = Hook { getHook } } =
            sortAttributes tools sort

-- ----------------------------------------------------------------
-- Translator
type VarContext p = Map p (SExpr, SExpr)

type Translator m p = MaybeT (StateT (VarContext p) (CounterT m))

evalTranslator
    :: Ord p
    => Monad m
    => Translator m p a
    -> MaybeT m a
evalTranslator = Morph.hoist (evalCounterT . flip evalStateT Map.empty)

runTranslator
    :: Ord p
    => Monad m
    => Translator m p a
    -> MaybeT m (a, VarContext p)
runTranslator = evalTranslator . includeState
  where includeState comp = do
            comp' <- comp
            state <- State.get
            pure (comp', state)
