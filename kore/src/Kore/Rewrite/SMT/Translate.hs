{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Rewrite.SMT.Translate (
    translatePredicateWith,
    Translator (..),
    TranslateItem (..),
    TranslatorState (..),
    SMTDependentAtom (..),
    translateSMTDependentAtom,
    evalTranslator,
    runTranslator,
    maybeToTranslator,
    -- For testing
    translatePattern,
) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error (
    MaybeT,
    hoistMaybe,
 )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Control.Monad.Counter (
    CounterT,
    MonadCounter,
    evalCounterT,
 )
import Control.Monad.Except
import Control.Monad.Morph as Morph
import Control.Monad.RWS.Strict (
    MonadReader,
    RWST (..),
    ask,
    evalRWST,
    local,
 )
import Control.Monad.State.Strict (
    MonadState,
 )
import qualified Control.Monad.State.Strict as State
import Data.Default
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product.Fields
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Reflection
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import Kore.Attribute.Hook
import Kore.Attribute.Smtlib
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import Kore.IndexedModule.MetadataTools
import Kore.Internal.InternalBool
import Kore.Internal.InternalInt
import Kore.Internal.Predicate hiding (
    AndF,
    BottomF,
    CeilF,
    EqualsF,
    ExistsF,
    FloorF,
    ForallF,
    IffF,
    ImpliesF,
    InF,
    NotF,
    OrF,
    TopF,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Log.WarnSymbolSMTRepresentation (
    warnSymbolSMTRepresentation,
 )
import Kore.Rewrite.SMT.Resolvers (
    translateSort,
    translateSymbol,
 )
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import Log (
    MonadLog (..),
 )
import Prelude.Kore
import SMT (
    SExpr (..),
 )
import qualified SMT
import qualified SMT.SimpleSMT as SimpleSMT

data TranslateItem variable
    = QuantifiedVariable !(ElementVariable variable)
    | UninterpretedTerm !(TermLike variable)

type TranslateTerm variable m =
    SExpr -> TranslateItem variable -> Translator variable m SExpr

-- ----------------------------------------------------------------
-- Predicate translation

{- | Translate a predicate for SMT.

The predicate may inhabit an arbitrary sort. Logical connectives are translated
to their SMT counterparts. Quantifiers, @\\ceil@, @\\floor@, and @\\in@ are
uninterpreted (translated as variables) as is @\\equals@ if its arguments are
not builtins or predicates. All other patterns are not translated and prevent
the predicate from being sent to SMT.
-}
translatePredicateWith ::
    forall p variable m.
    ( Given (SmtMetadataTools Attribute.Symbol)
    , p ~ TermLike variable
    , MonadLog m
    , InternalVariable variable
    ) =>
    SideCondition variable ->
    TranslateTerm variable m ->
    Predicate variable ->
    Translator variable m SExpr
translatePredicateWith sideCondition translateTerm predicate =
    translatePredicatePattern $
        fromPredicate_ predicate
  where
    translatePredicatePattern :: p -> Translator variable m SExpr
    translatePredicatePattern pat
        | SideCondition.isDefined sideCondition pat =
            withDefinednessAssumption $
                translatePredicatePatternWorker pat
        | otherwise = translatePredicatePatternWorker pat

    translatePredicatePatternWorker :: p -> Translator variable m SExpr
    translatePredicatePatternWorker pat =
        case Cofree.tailF (Recursive.project pat) of
            -- Logical connectives: translate as connectives
            AndF and' -> translatePredicateAnd and'
            BottomF _ -> return (SMT.bool False)
            EqualsF eq ->
                -- Equality of predicates and builtins can be translated to
                -- equality in the SMT solver, but other patterns must remain
                -- uninterpreted.
                translatePredicateEquals eq
                    <|> translateUninterpreted translateTerm SMT.tBool pat
            IffF iff -> translatePredicateIff iff
            ImpliesF implies -> translatePredicateImplies implies
            NotF not' -> translatePredicateNot not'
            OrF or' -> translatePredicateOr or'
            TopF _ -> return (SMT.bool True)
            -- Uninterpreted: translate as variables
            CeilF _ -> translateUninterpreted translateTerm SMT.tBool pat
            ExistsF exists' ->
                translatePredicateExists exists'
                    <|> translateUninterpreted translateTerm SMT.tBool pat
            FloorF _ -> translateUninterpreted translateTerm SMT.tBool pat
            ForallF forall' ->
                translatePredicateForall forall'
                    <|> translateUninterpreted translateTerm SMT.tBool pat
            InF _ -> translateUninterpreted translateTerm SMT.tBool pat
            -- Invalid: no translation, should not occur in predicates
            MuF _ -> empty
            NuF _ -> empty
            ApplySymbolF _ -> empty
            InjF _ -> empty
            ApplyAliasF _ -> empty
            DomainValueF _ -> empty
            NextF _ -> empty
            RewritesF _ -> empty
            VariableF _ -> empty
            StringLiteralF _ -> empty
            InternalBoolF _ -> empty
            InternalBytesF _ -> empty
            InternalIntF _ -> empty
            InternalStringF _ -> empty
            InternalListF _ -> empty
            InternalMapF _ -> empty
            InternalSetF _ -> empty
            InhabitantF _ -> empty
            EndiannessF _ -> empty
            SignednessF _ -> empty

    translatePredicateAnd And{andFirst, andSecond} =
        SMT.and
            <$> translatePredicatePattern andFirst
            <*> translatePredicatePattern andSecond

    translatePredicateEquals
        Equals
            { equalsOperandSort
            , equalsFirst
            , equalsSecond
            } =
            SMT.eq
                <$> translatePredicateEqualsChild equalsFirst
                <*> translatePredicateEqualsChild equalsSecond
          where
            translatePredicateEqualsChild child =
                -- Attempt to translate patterns in builtin sorts, or failing that,
                -- as predicates.
                (<|>)
                    (translatePattern sideCondition translateTerm equalsOperandSort child)
                    (translatePredicatePattern child)

    translatePredicateIff Iff{iffFirst, iffSecond} =
        iff
            <$> translatePredicatePattern iffFirst
            <*> translatePredicatePattern iffSecond
      where
        iff a b = SMT.and (SMT.implies a b) (SMT.implies b a)

    translatePredicateImplies Implies{impliesFirst, impliesSecond} =
        SMT.implies
            <$> translatePredicatePattern impliesFirst
            <*> translatePredicatePattern impliesSecond

    translatePredicateNot Not{notChild} =
        SMT.not <$> translatePredicatePattern notChild

    translatePredicateOr Or{orFirst, orSecond} =
        SMT.or
            <$> translatePredicatePattern orFirst
            <*> translatePredicatePattern orSecond

    translatePredicateExists ::
        Exists Sort variable p -> Translator variable m SExpr
    translatePredicateExists Exists{existsVariable, existsChild} =
        translateQuantifier SMT.existsQ existsVariable existsChild

    translatePredicateForall ::
        Forall Sort variable p -> Translator variable m SExpr
    translatePredicateForall Forall{forallVariable, forallChild} =
        translateQuantifier SMT.forallQ forallVariable forallChild

    translateQuantifier ::
        ([SExpr] -> SExpr -> SExpr) ->
        ElementVariable variable ->
        p ->
        Translator variable m SExpr
    translateQuantifier quantifier var predTerm = do
        smtSort <- translateVariableSort
        oldVar <- State.gets (Map.lookup var . quantifiedVars)
        smtVar <- translateTerm smtSort (QuantifiedVariable var)
        smtPred <- translatePredicatePattern predTerm
        field @"quantifiedVars"
            Lens.%= maybe (Map.delete var) (Map.insert var) oldVar
        return $ quantifier [SMT.List [smtVar, smtSort]] smtPred
      where
        Variable{variableSort} = var
        translateVariableSort :: Translator variable m SExpr
        translateVariableSort =
            case getHook of
                Just builtinSort
                    | builtinSort == Builtin.Bool.sort -> pure SMT.tBool
                    | builtinSort == Builtin.Int.sort -> pure SMT.tInt
                _ -> translateSort variableSort & maybeToTranslator
        tools :: SmtMetadataTools Attribute.Symbol
        tools = given
        Attribute.Sort{hook = Hook{getHook}} =
            sortAttributes tools variableSort

{- | Attempt to translate an arbitrary ML pattern for the solver.
 It should only be used in the 'Predicate' translator or in
 the tests.
-}
translatePattern ::
    forall variable monad.
    Given (SmtMetadataTools Attribute.Symbol) =>
    MonadLog monad =>
    InternalVariable variable =>
    SideCondition variable ->
    TranslateTerm variable monad ->
    Sort ->
    TermLike variable ->
    Translator variable monad SExpr
translatePattern sideCondition translateTerm sort pat =
    case getHook of
        Just builtinSort
            | builtinSort == Builtin.Bool.sort -> translateBool pat
            | builtinSort == Builtin.Int.sort -> translateInt pat
        _ -> case Cofree.tailF $ Recursive.project pat of
            VariableF _ -> do
                smtSort <- maybeToTranslator $ translateSort sort
                translateUninterpreted translateTerm smtSort pat
            ApplySymbolF app ->
                translateApplication (translateSort sort) pat app
            _ -> empty
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = given
    Attribute.Sort{hook = Hook{getHook}} =
        sortAttributes tools sort

    translateInt :: TermLike variable -> Translator variable monad SExpr
    translateInt pat'
        | SideCondition.isDefined sideCondition pat' =
            withDefinednessAssumption $
                translateIntWorker pat'
        | otherwise =
            translateIntWorker pat'

    translateIntWorker :: TermLike variable -> Translator variable monad SExpr
    translateIntWorker pat' =
        case Cofree.tailF (Recursive.project pat') of
            VariableF _ -> translateUninterpreted translateTerm SMT.tInt pat'
            InternalIntF (Const InternalInt{internalIntValue}) ->
                return $ SMT.int internalIntValue
            ApplySymbolF app ->
                translateApplication (Just SMT.tInt) pat' app
            _ -> empty
    translateBool :: TermLike variable -> Translator variable monad SExpr
    translateBool pat'
        | SideCondition.isDefined sideCondition pat' =
            withDefinednessAssumption $
                translateBoolWorker pat'
        | otherwise =
            translateBoolWorker pat'

    translateBoolWorker :: TermLike variable -> Translator variable monad SExpr
    translateBoolWorker pat' =
        case Cofree.tailF (Recursive.project pat') of
            VariableF _ -> translateUninterpreted translateTerm SMT.tBool pat'
            InternalBoolF (Const InternalBool{internalBoolValue}) ->
                return $ SMT.bool internalBoolValue
            NotF Not{notChild} ->
                -- \not is equivalent to BOOL.not for functional patterns.
                -- The following is safe because non-functional patterns
                -- will fail to translate.
                SMT.not <$> translateBool notChild
            ApplySymbolF app ->
                translateApplication (Just SMT.tBool) pat' app
            _ -> empty

    translateApplication ::
        Maybe SExpr ->
        TermLike variable ->
        Application Symbol (TermLike variable) ->
        Translator variable monad SExpr
    translateApplication
        maybeSort
        original
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            } =
            -- TODO: This would send interpreted symbols to the solver
            -- even if they may not be defined. We should only send symbols
            -- we know to be defined.
            translateInterpretedApplication
                <|> translateUninterpreted'
          where
            guardLocalFunctionalPattern
                | isFunctionalPattern original = return ()
                | otherwise = do
                    TranslatorEnv{assumeDefined} <- ask
                    Monad.guard (assumeDefined && isFunctionPattern original)
            translateInterpretedApplication = do
                let translated = translateSymbol applicationSymbolOrAlias
                sexpr <- maybe warnAndDiscard return translated
                children <-
                    zipWithM
                        (translatePattern sideCondition translateTerm)
                        applicationChildrenSorts
                        applicationChildren
                return $ shortenSExpr (applySExpr sexpr children)
            applicationChildrenSorts = termLikeSort <$> applicationChildren
            warnAndDiscard =
                warnSymbolSMTRepresentation applicationSymbolOrAlias
                    >> empty
            translateUninterpreted' = do
                guardLocalFunctionalPattern
                sort' <- maybeToTranslator maybeSort
                translateUninterpreted translateTerm sort' original

translateUninterpreted ::
    TranslateTerm variable m ->
    SExpr ->
    TermLike variable ->
    Translator variable m SExpr
translateUninterpreted translateTerm sExpr pat =
    translateTerm sExpr (UninterpretedTerm pat)

{- | Represents the SMT encoding of an untranslatable pattern containing
occurrences of existential variables.  Since the same pattern might appear
under different instances of the same existential quantifiers, it is made
dependent on the name of the variables, which must be instantiated with
the current encodings corresponding to those variables when transformed to a
proper 'SExpr'. See 'translateSMTDependentAtom'.
-}
data SMTDependentAtom variable = SMTDependentAtom
    { smtName :: !Text
    , smtType :: !SExpr
    , boundVars :: ![ElementVariable variable]
    }
    deriving stock (Eq, GHC.Generic, Show)

{- | Instantiates an 'SMTDependentAtom' with the current encodings for the
variables it depends on.

May fail (return 'empty') if any of the variables it depends on are not
currently existentially quantified.
-}
translateSMTDependentAtom ::
    InternalVariable variable =>
    SMT.MonadSMT m =>
    Map.Map (ElementVariable variable) (SMTDependentAtom variable) ->
    SMTDependentAtom variable ->
    Translator variable m SExpr
translateSMTDependentAtom
    quantifiedVars
    SMTDependentAtom{smtName = funName, boundVars} =
        maybe empty (return . SimpleSMT.fun funName) boundEncodings
      where
        boundEncodings =
            for boundVars $
                \name -> SMT.Atom . smtName <$> Map.lookup name quantifiedVars

-- ----------------------------------------------------------------
-- Translator
data TranslatorState variable = TranslatorState
    { terms :: !(Map (TermLike variable) (SMTDependentAtom variable))
    , freeVars :: !(Map (ElementVariable variable) SExpr)
    , quantifiedVars ::
        !(Map (ElementVariable variable) (SMTDependentAtom variable))
    }
    deriving stock (Eq, GHC.Generic, Show)

instance Default (TranslatorState variable) where
    def = TranslatorState def def def

{- | Translator local environment, used to check if a subterm is
 assumed to be defined. If it is, we can translate it for the solver.
-}
newtype TranslatorEnv = TranslatorEnv {assumeDefined :: Bool}

instance Default TranslatorEnv where
    def = TranslatorEnv False

newtype Translator variable m a = Translator
    { getTranslator ::
        MaybeT
            ( RWST
                TranslatorEnv
                ()
                (TranslatorState variable)
                (CounterT m)
            )
            a
    }
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (Alternative)
    deriving newtype (MonadCounter, MonadLog)
    deriving newtype (MonadReader TranslatorEnv)
    deriving newtype (MonadState (TranslatorState variable))

instance MonadTrans (Translator variable) where
    lift = Translator . lift . lift . lift

instance MFunctor (Translator variable) where
    hoist f (Translator translator) =
        hoist (hoist (hoist f)) translator
            & Translator

instance SMT.MonadSMT m => SMT.MonadSMT (Translator variable m)

instance MonadSimplify m => MonadSimplify (Translator variable m)

evalTranslator :: Monad m => Translator p m a -> MaybeT m a
evalTranslator (Translator translator) =
    Morph.hoist (evalCounterT . evalRST def def) translator
  where
    evalRST env state rwst = do
        (result, _) <- evalRWST rwst env state
        return result

runTranslator :: Monad m => Translator p m a -> MaybeT m (a, TranslatorState p)
runTranslator = evalTranslator . includeState
  where
    includeState comp = do
        comp' <- comp
        state <- State.get
        pure (comp', state)

maybeToTranslator :: Monad m => Maybe a -> Translator p m a
maybeToTranslator = Translator . hoistMaybe

withDefinednessAssumption :: Monad m => Translator p m a -> Translator p m a
withDefinednessAssumption =
    local (const $ TranslatorEnv True)
