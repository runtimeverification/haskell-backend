{-|
Module      : Kore.Step.SmtLemma
Description : Declares all rules marked smt-lemma to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.SmtLemma
    ( declareSMTLemmas
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Error
                 ( runMaybeT )
import qualified Control.Monad.Counter as Counter
import           Control.Monad.Except
import qualified Control.Monad.State as State
import           Control.Monad.Trans.Maybe
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import           Data.Reflection
import qualified Data.Text as Text

import           Kore.AST.Kore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.Attribute.SmtLemma
import           Kore.Attribute.Smtlib
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.Step.AxiomPatterns
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
import           Kore.Step.TranslateSMT
import           Kore.Unparser
import           SMT
                 ( MonadSMT, SExpr (..), SMT )
import qualified SMT

normalizeRule
    :: ( Ord (var Object)
       , Unparse (var Object)
       )
    => StepPattern Object var
    -> StepPattern Object var
normalizeRule pat =
    case pat of
        Rewrites_ s a b -> mkEquals s a b -- `s` is arbitrary/dummy value
        Implies_ s a (Next_ _ b) -> mkEquals s a b
        And_ _ a b -> mkAnd (normalizeRule a) (normalizeRule b)
        Implies_ _ a b -> mkImplies (normalizeRule a) (normalizeRule b)
        _ -> pat

-- | Given an indexed module, `declareSMTLemmas` translates all
-- rewrite rules marked with the smt-lemma attribute into the
-- smt2 standard, and sends them to the current SMT solver.
-- it assumes all symbols in all smt-lemma rules have been
-- declared in the smt prelude.
declareSMTLemmas
    :: forall m param dom .
        ( MonadSMT m
        , Traversable dom
        , dom ~ Domain.Builtin
        , Given (MetadataTools Object StepperAttributes)
        )
    => IndexedModule
            param (KorePattern dom Variable (Unified (Valid (Unified Variable))))
            StepperAttributes
            AxiomPatternAttributes
    -> m ()
declareSMTLemmas m = SMT.liftSMT $ do
    mapM_ declareSort (indexedModuleObjectSortDescriptions m)
    mapM_ declareSymbol (indexedModuleObjectSymbolSentences m)
    mapM_ declareRule (indexedModuleAxioms m)
  where
    declareSort :: forall .
        ( Given (MetadataTools Object StepperAttributes)
        )
        =>  ( StepperAttributes
            , SentenceSort
                Object
                (KorePattern Domain.Builtin Variable (Unified (Valid (Unified Variable))))
            )
            -> SMT ()
    declareSort (atts, _) =
        case getSmtlib $ smtlib atts of
            Just (SMT.List (SMT.Atom name : sortArgs)) -> do
                _ <- SMT.declareSort name (length sortArgs)
                pure ()
            _ -> pure ()
    declareSymbol :: forall .
        ( Given (MetadataTools Object StepperAttributes)
        )
        =>  ( StepperAttributes
            , SentenceSymbol
                Object
                (KorePattern Domain.Builtin Variable (Unified (Valid (Unified Variable))))
            )
            -> SMT (Maybe ())
    declareSymbol (atts, symDeclaration) = runMaybeT $
        case getSmtlib $ smtlib atts of
            Just (SMT.List (SMT.Atom name : _)) -> do
                inputSorts <- mapM translateSort (sentenceSymbolSorts symDeclaration)
                resultSort <- translateSort (sentenceSymbolResultSort symDeclaration)
                _ <- SMT.declareFun name inputSorts resultSort
                pure ()
            _ -> pure ()
    declareRule :: forall sortParam .
        ( Given (MetadataTools Object StepperAttributes)
        )
        =>  ( AxiomPatternAttributes
            , SentenceAxiom
                sortParam
                (KorePattern Domain.Builtin Variable (Unified (Valid (Unified Variable))))
            )
            -> SMT (Maybe ())
    declareRule (atts, axiomDeclaration) = runMaybeT $ do
        guard (isSmtLemma $ smtLemma atts)
        pat <- getRight
            $ fromKorePattern Object
            $ sentenceAxiomPattern axiomDeclaration
        (lemma, vars) <-
            runTranslator
          $ translatePredicate translateUninterpreted
          $ wrapPredicate
          $ normalizeRule pat
        SMT.assert (addQuantifiers vars lemma)

    addQuantifiers vars lemma | null vars = lemma
    addQuantifiers vars lemma = SMT.List
        [ SMT.Atom "forall"
        , SMT.List
            [ SMT.List [sexpr, t] | (sexpr, t) <- Map.elems vars ]
        , lemma
        ]

    translateSort
        :: Given (MetadataTools Object StepperAttributes)
        => Sort Object
        -> MaybeT SMT SExpr
    translateSort sort@(SortActualSort (SortActual _ children)) =
        case getSmtlib $ smtlib $ sortAttributes given sort of
            Just sExpr -> do
                children' <- mapM translateSort children
                pure $ applySExpr sExpr children'
            Nothing -> mzero
    translateSort _ = mzero

getRight :: MonadPlus m => Either a b -> m b
getRight (Right a) = pure a
getRight _ = mzero

translateUninterpreted
    :: ( Ord p
       , p ~ StepPattern Object variable
       , Unparse (variable Object)
       )
    => SExpr  -- ^ type name
    -> p  -- ^ uninterpreted pattern
    -> Translator p SExpr
translateUninterpreted t pat | isVariable pat =
    lookupPattern <|> freeVariable
  where
    isVariable p =
        case Cofree.tailF $ Recursive.project p of
            VariablePattern _ -> True
            _ -> False
    lookupPattern = do
        result <- State.gets $ Map.lookup pat
        maybe empty (return . fst) result
    freeVariable = do
        n <- Counter.increment
        let var = SMT.Atom ("<" <> Text.pack (show n) <> ">")
        State.modify' (Map.insert pat (var, t))
        return var
translateUninterpreted _ _ = empty
