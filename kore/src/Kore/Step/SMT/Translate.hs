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
    ( translatePredicateWith
    , Translator
    , TranslateItem (..)
    , TranslatorState (..)
    , SMTDependentAtom (..)
    , translateSMTDependentAtom
    , evalTranslator
    , runTranslator
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( MaybeT
    , hoistMaybe
    )
import qualified Control.Lens as Lens
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
import Data.Default
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product.Fields
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Reflection
import Data.Text
    ( Text
    )
import qualified GHC.Generics as GHC

import Kore.Attribute.Hook
import Kore.Attribute.Smtlib
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import Kore.IndexedModule.MetadataTools
import Kore.Internal.Predicate
import Kore.Internal.TermLike
import Kore.Log.WarnSymbolSMTRepresentation
    ( warnSymbolSMTRepresentation
    )
import qualified Kore.Sort as Sort
import Kore.Step.SMT.Resolvers
    ( translateSort
    , translateSymbol
    )
import Log
    ( MonadLog (..)
    )
import SMT
    ( SExpr (..)
    )
import qualified SMT
import qualified SMT.SimpleSMT as SimpleSMT


data TranslateItem variable
    = QuantifiedVariable !(ElementVariable variable)
    | UninterpretedTerm !(TermLike variable)

-- ----------------------------------------------------------------
-- Predicate translation

{- | Translate a predicate for SMT.

The predicate may inhabit an arbitrary sort. Logical connectives are translated
to their SMT counterparts. Quantifiers, @\\ceil@, @\\floor@, and @\\in@ are
uninterpreted (translated as variables) as is @\\equals@ if its arguments are
not builtins or predicates. All other patterns are not translated and prevent
the predicate from being sent to SMT.

 -}
translatePredicateWith
    :: forall p variable m .
        ( Given (SmtMetadataTools Attribute.Symbol)
        , p ~ TermLike variable
        , MonadLog m
        , InternalVariable variable
        )
    => (SExpr -> TranslateItem variable -> Translator m variable SExpr)
    -> Predicate variable
    -> Translator m variable SExpr
translatePredicateWith translateTerm predicate =
    translatePredicatePattern
    $ unwrapPredicate
    $ coerceSort Sort.predicateSort predicate
  where
    translateUninterpreted t pat = translateTerm t (UninterpretedTerm pat)
    translatePredicatePattern :: p -> Translator m variable SExpr
    translatePredicatePattern pat =
        case Cofree.tailF (Recursive.project pat) of
            EvaluatedF child -> translatePredicatePattern (getEvaluated child)
            DefinedF child -> translatePredicatePattern (getDefined child)
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
            ExistsF exists' ->
                translatePredicateExists exists'
                <|> translateUninterpreted SMT.tBool pat
            FloorF _ -> translateUninterpreted SMT.tBool pat
            ForallF forall' ->
                translatePredicateForall forall'
                <|> translateUninterpreted SMT.tBool pat
            InF _ -> translateUninterpreted SMT.tBool pat

            -- Invalid: no translation, should not occur in predicates
            MuF _ -> empty
            NuF _ -> empty
            ApplySymbolF _ -> empty
            InjF _ -> empty
            ApplyAliasF _ -> empty
            BuiltinF _ -> empty
            DomainValueF _ -> empty
            NextF _ -> empty
            RewritesF _ -> empty
            VariableF _ -> empty
            StringLiteralF _ -> empty
            InternalBytesF _ -> empty
            InhabitantF _ -> empty
            EndiannessF _ -> empty
            SignednessF _ -> empty

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
    translateInt :: p -> Translator m variable SExpr
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
            DefinedF (Defined child) -> translateInt child
            _ -> empty

    -- | Translate a functional pattern in the builtin Bool sort for SMT.
    translateBool :: p -> Translator m variable SExpr
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
            DefinedF (Defined child) -> translateBool child
            _ -> empty

    translateApplication :: Application Symbol p -> Translator m variable SExpr
    translateApplication
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
      = do
        let translated = translateSymbol applicationSymbolOrAlias
        sexpr <- maybe empty return translated
        when (isNothing translated)
            $ warnSymbolSMTRepresentation applicationSymbolOrAlias
        children <- zipWithM translatePattern
            applicationChildrenSorts
            applicationChildren
        return $ shortenSExpr (applySExpr sexpr children)
      where
        applicationChildrenSorts = termLikeSort <$> applicationChildren

    translatePredicateExists
        :: Exists Sort variable p -> Translator m variable SExpr
    translatePredicateExists Exists { existsVariable, existsChild } =
        translateQuantifier SMT.existsQ existsVariable existsChild

    translatePredicateForall
        :: Forall Sort variable p -> Translator m variable SExpr
    translatePredicateForall Forall { forallVariable, forallChild } =
        translateQuantifier SMT.forallQ forallVariable forallChild

    translateQuantifier
        :: ([SExpr] -> SExpr -> SExpr)
        -> ElementVariable variable
        -> p
        -> Translator m variable SExpr
    translateQuantifier quantifier var predTerm = do
        smtSort <- translateVariableSort
        oldVar <- State.gets (Map.lookup var . quantifiedVars)
        smtVar <- translateTerm smtSort (QuantifiedVariable var)
        smtPred <- translatePredicatePattern predTerm
        field @"quantifiedVars" Lens.%=
            maybe (Map.delete var) (Map.insert var) oldVar
        return $ quantifier [SMT.List [smtVar, smtSort]] smtPred
      where
        Variable { variableSort } = var
        translateVariableSort =
            case getHook of
              Just builtinSort
                | builtinSort == Builtin.Bool.sort -> pure SMT.tBool
                | builtinSort == Builtin.Int.sort  -> pure SMT.tInt
              _ -> translateSort variableSort & hoistMaybe
        tools :: SmtMetadataTools Attribute.Symbol
        tools = given
        Attribute.Sort { hook = Hook { getHook } } =
            sortAttributes tools variableSort

    translatePattern :: Sort -> p -> Translator m variable SExpr
    translatePattern sort pat =
        case getHook of
            Just builtinSort
              | builtinSort == Builtin.Bool.sort -> translateBool pat
              | builtinSort == Builtin.Int.sort -> translateInt pat
            _ -> case Cofree.tailF $ Recursive.project pat of
                    VariableF _ -> translateUninterpreted'
                    ApplySymbolF app
                      | isFunctionalPattern pat ->
                          translateApplication app
                          <|> translateUninterpreted'
                      | otherwise ->
                          translateApplication app
                    DefinedF (Defined child) -> translatePattern sort child
                    _ -> empty
      where
        tools :: SmtMetadataTools Attribute.Symbol
        tools = given
        Attribute.Sort { hook = Hook { getHook } } =
            sortAttributes tools sort
        translateUninterpreted' = do
            smtSort <- hoistMaybe $ translateSort sort
            translateUninterpreted smtSort pat

{-| Represents the SMT encoding of an untranslatable pattern containing
occurrences of existential variables.  Since the same pattern might appear
under different instances of the same existential quantifiers, it is made
dependent on the name of the variables, which must be instantiated with
the current encodings corresponding to those variables when transformed to a
proper 'SExpr'. See 'translateSMTDependentAtom'.
-}
data SMTDependentAtom variable = SMTDependentAtom
    { smtName   :: !Text
    , smtType   :: !SExpr
    , boundVars :: ![ElementVariable variable]
    }
    deriving (Eq, GHC.Generic, Show)

{-| Instantiates an 'SMTDependentAtom' with the current encodings for the
variables it depends on.

May fail (return 'empty') if any of the variables it depends on are not
currently existentially quantified.
-}
translateSMTDependentAtom
    :: InternalVariable variable
    => SMT.MonadSMT m
    => Map.Map (ElementVariable variable) (SMTDependentAtom variable)
    -> SMTDependentAtom variable
    -> Translator m variable SExpr
translateSMTDependentAtom
    quantifiedVars
    SMTDependentAtom { smtName = funName, boundVars }
  =
    maybe empty (return . SimpleSMT.fun funName) boundEncodings
  where
    boundEncodings =
        for boundVars
            $ \name -> SMT.Atom . smtName <$> Map.lookup name quantifiedVars

-- ----------------------------------------------------------------
-- Translator
data TranslatorState variable
    = TranslatorState
        { terms :: !(Map (TermLike variable) (SMTDependentAtom variable))
        , freeVars :: !(Map (ElementVariable variable) SExpr)
        , quantifiedVars ::
            !(Map (ElementVariable variable) (SMTDependentAtom variable))
        }
    deriving (Eq, GHC.Generic, Show)

instance Default (TranslatorState variable) where
    def = TranslatorState def def def

type Translator m variable =
    MaybeT (StateT (TranslatorState variable) (CounterT m))

evalTranslator :: Monad m => Translator m p a -> MaybeT m a
evalTranslator = Morph.hoist (evalCounterT . flip evalStateT def)

runTranslator :: Monad m => Translator m p a -> MaybeT m (a, TranslatorState p)
runTranslator = evalTranslator . includeState
  where includeState comp = do
            comp' <- comp
            state <- State.get
            pure (comp', state)
