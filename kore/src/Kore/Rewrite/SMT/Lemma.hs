{- |
Module      : Kore.Rewrite.SMT.Lemma
Description : Declares all rules marked smt-lemma to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.SMT.Lemma (
    declareSMTLemmas,
) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error (
    runMaybeT,
 )
import qualified Control.Lens as Lens
import qualified Control.Monad.Counter as Counter
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product.Fields
import qualified Data.Map.Strict as Map
import Data.Reflection
import qualified Data.Text as Text
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.SmtLemma
import Kore.Attribute.Symbol
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.MetadataTools
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Symbol as Internal.Symbol
import Kore.Internal.TermLike
import qualified Kore.Rewrite.SMT.Declaration.All as SMT.All (
    declare,
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
    SMT.All.declare (smtData tools)
    mapM_ declareRule (indexedModuleAxioms m)
    result <- SMT.check
    when (isUnsatisfiable result) errorInconsistentDefinitions
  where
    tools :: SmtMetadataTools StepperAttributes
    tools = given

    declareRule ::
        ( Attribute.Axiom Internal.Symbol.Symbol VariableName
        , SentenceAxiom (TermLike VariableName)
        ) ->
        m (Maybe ())
    declareRule (atts, axiomDeclaration) = runMaybeT $ do
        guard (isSmtLemma $ Attribute.smtLemma atts)
        (lemma, TranslatorState{terms}) <-
            runTranslator $
                translatePredicateWith SideCondition.top translateUninterpreted $
                    wrapPredicate $ sentenceAxiomPattern axiomDeclaration
        SMT.assert (addQuantifiers terms lemma)

    addQuantifiers vars lemma | null vars = lemma
    addQuantifiers vars lemma =
        SMT.List
            [ SMT.Atom "forall"
            , SMT.List
                [ SMT.List [SMT.Atom smtName, smtType]
                | SMTDependentAtom{smtName, smtType} <- Map.elems vars
                ]
            , lemma
            ]

    isUnsatisfiable Unsat = True
    isUnsatisfiable _ = False
    ~errorInconsistentDefinitions =
        error "The definitions sent to the solver are inconsistent."

translateUninterpreted ::
    forall m variable.
    ( Ord variable
    , Monad m
    ) =>
    -- | type name
    SExpr ->
    -- | uninterpreted pattern
    TranslateItem variable ->
    Translator variable m SExpr
translateUninterpreted _ (QuantifiedVariable _) =
    empty
translateUninterpreted t (UninterpretedTerm pat)
    | isVariable pat =
        lookupPattern <|> freeVariable
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
