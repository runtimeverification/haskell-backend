{- |
Module      : Kore.Rewrite.SMT.Lemma
Description : Declares all rules marked smt-lemma to the SMT solver.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.SMT.Lemma (
    declareSMTLemmas,
) where

import Control.Comonad.Trans.Cofree qualified as Cofree
import Control.Error (
    hoistMaybe,
    hush,
    runMaybeT,
 )
import Control.Lens qualified as Lens
import Control.Monad.Counter qualified as Counter
import Control.Monad.Except
import Control.Monad.State qualified as State
import Data.Functor.Foldable qualified as Recursive
import Data.Generics.Product.Fields
import Data.Map.Strict qualified as Map
import Data.Reflection
import Data.Text qualified as Text
import Kore.Attribute.Axiom qualified as Attribute
import Kore.Attribute.SmtLemma
import Kore.Attribute.Symbol
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.MetadataTools
import Kore.Internal.Predicate
import Kore.Internal.SideCondition (
    top,
 )
import Kore.Internal.Symbol qualified as Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewrite.SMT.Declaration (
    declareSortsSymbols,
 )
import Kore.Rewrite.SMT.Translate
import Kore.Syntax.Sentence (
    SentenceAxiom (..),
 )
import Log (
    MonadLog (..),
 )
import Prelude.Kore
import SMT (
    MonadSMT (..),
    Result (..),
    SExpr (..),
 )

{- | Given an indexed module, `declareSMTLemmas` translates all
 rewrite rules marked with the smt-lemma attribute into the
 smt2 standard, and sends them to the current SMT solver.
 It assumes that all symbols in all smt-lemma rules either have been
 declared in the smt prelude or they have an smtlib attribute.
 This function will throw an error if the definitions sent to
 the solver are inconsistent.
-}
declareSMTLemmas ::
    forall m.
    ( Given (SmtMetadataTools StepperAttributes)
    , MonadIO m
    , MonadSMT m
    , MonadLog m
    ) =>
    VerifiedModule StepperAttributes ->
    m ()
declareSMTLemmas m = do
    declareSortsSymbols $ smtData tools
    mapM_ declareRule $ indexedModuleAxioms m
    isUnsatisfiable <- (Unsat ==) <$> SMT.check
    when isUnsatisfiable errorInconsistentDefinitions
  where
    tools :: SmtMetadataTools StepperAttributes
    tools = given

    declareRule ::
        ( Attribute.Axiom Internal.Symbol.Symbol VariableName
        , SentenceAxiom (TermLike VariableName)
        ) ->
        m (Maybe ())
    declareRule (atts, axiomDeclaration) = runMaybeT $ do
        guard $ isSmtLemma $ Attribute.smtLemma atts
        oldAxiomEncoding <-
            sentenceAxiomPattern axiomDeclaration
                & convert
                & hoistMaybe
        (lemma, TranslatorState{terms, predicates}) <-
            oldAxiomEncoding
                & wrapPredicate
                & translatePredicateWith top translateUninterpreted
                & runTranslator
        addQuantifiers (Map.elems terms <> Map.elems predicates) lemma
            & SMT.assert

    -- Translate an "unparsed" equation for Z3.
    -- Convert new encoding back to old.
    -- See https://github.com/runtimeverification/k/pull/2061#issuecomment-927922217
    convert :: TermLike VariableName -> Maybe (TermLike VariableName)
    convert
        ( Implies_
                impliesSort
                requires
                ( Equals_
                        _ -- equalsOperandSort
                        _ -- equalsResultSort
                        left
                        ( And_
                                _ -- andSort
                                right
                                ensures
                            )
                    )
            ) = do
            requiresPredicate <- hush $ makePredicate requires
            ensuresPredicate <- hush $ makePredicate ensures
            Just $
                fromPredicate impliesSort $
                    makeImpliesPredicate
                        requiresPredicate
                        ( makeAndPredicate
                            ( makeEqualsPredicate
                                left
                                right
                            )
                            ensuresPredicate
                        )
    convert termLike = Just termLike

    addQuantifiers :: [SMTDependentAtom variable] -> SExpr -> SExpr
    addQuantifiers smtDependentAtoms lemma | null smtDependentAtoms = lemma
    addQuantifiers smtDependentAtoms lemma =
        SMT.List
            [ SMT.Atom "forall"
            , SMT.List
                [ SMT.List [SMT.Atom smtName, smtType]
                | SMTDependentAtom{smtName, smtType} <- smtDependentAtoms
                ]
            , lemma
            ]

    ~errorInconsistentDefinitions =
        error "The definitions sent to the solver are inconsistent."

translateUninterpreted ::
    ( Ord variable
    , Monad m
    ) =>
    -- | type name
    SExpr ->
    -- | uninterpreted pattern
    TranslateItem variable ->
    Translator variable m SExpr
translateUninterpreted _ (QuantifiedVariable _) = empty
translateUninterpreted _ (UninterpretedPredicate _) = empty
translateUninterpreted t (UninterpretedTerm pat)
    | isVariable pat = lookupPattern <|> freeVariable
    | otherwise = empty
  where
    isVariable p =
        case Cofree.tailF $ Recursive.project p of
            VariableF _ -> True
            _ -> False
    lookupPattern = do
        result <- State.gets $ Map.lookup pat . terms
        maybe empty (return . SMT.Atom . smtName) result
    freeVariable = do
        n <- Counter.increment
        let var = "<" <> Text.pack (show n) <> ">"
        field @"terms"
            Lens.%= Map.insert
                pat
                SMTDependentAtom{smtName = var, smtType = t, boundVars = []}
        return $ SMT.Atom var
