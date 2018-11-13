{-|
Module      : Kore.SMT.SMT
Description : Basic SMT interface.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.SMT.SMT
    ( unsafeTryRefutePredicate
    , translatePredicate
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT, runMaybeT )
import           Control.Monad.Except
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Proxy
import           Data.Reflection
                 ( Given (..) )
import qualified Data.Text as Text
import           Prelude hiding
                 ( and, not, or )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (applicationSortsOperands) )
import           Kore.Attribute.Hook
import           Kore.Attribute.Smtlib
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Builtin.Int
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Kore
import           Kore.SMT.Translator
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           SMT
                 ( Result (..), SExpr (..), SMT )
import qualified SMT

{- | Attempt to disprove the given predicate using SMT.

 -}
unsafeTryRefutePredicate
    :: forall level variable .
       ( Given (MetadataTools level StepperAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , SortedVariable variable
       )
    => Kore.Predicate level variable
    -> Maybe Bool
unsafeTryRefutePredicate korePredicate =
    case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta   -> Nothing
        IsObject ->
            SMT.unsafeRunSMT SMT.defaultConfig $ runMaybeT session
          where
            session = do
                smtPredicate <- translatePredicate korePredicate
                SMT.assert smtPredicate
                result <- SMT.check
                case result of
                    Unsat -> return False
                    _ -> empty

{- | Translate a predicate for SMT.

The predicate may inhabit an arbitrary sort. Logical connectives are translated
to their SMT counterparts. Quantifiers, @\\ceil@, @\\floor@, and @\\in@ are
uninterpreted (translated as variables) as is @\\equals@ if its arguments are
not builtins or predicates. All other patterns are not translated and prevent
the predicate from being sent to SMT.

 -}
translatePredicate
    :: forall variable.
        (Ord (variable Object), Given (MetadataTools Object StepperAttributes))
    => Kore.Predicate Object variable
    -> MaybeT SMT SExpr
translatePredicate predicate = do
    let translator = translatePredicatePattern $ Kore.unwrapPredicate predicate
    runTranslator translator
  where
    translatePredicatePattern
        :: PureMLPattern Object variable
        -> Translator (PureMLPattern Object variable) SExpr
    translatePredicatePattern pat =
        case Functor.Foldable.project pat of
            -- Logical connectives: translate as connectives
            AndPattern and -> translatePredicateAnd and
            BottomPattern _ -> return (SMT.bool False)
            EqualsPattern eq ->
                -- Equality of predicates and builtins can be translated to
                -- equality in the SMT solver, but other patterns must remain
                -- uninterpreted.
                translatePredicateEquals eq <|> translateUninterpretedBool pat
            IffPattern iff -> translatePredicateIff iff
            ImpliesPattern implies -> translatePredicateImplies implies
            NotPattern not -> translatePredicateNot not
            OrPattern or -> translatePredicateOr or
            TopPattern _ -> return (SMT.bool True)

            -- Uninterpreted: translate as variables
            CeilPattern _ -> translateUninterpretedBool pat
            ExistsPattern _ -> translateUninterpretedBool pat
            FloorPattern _ -> translateUninterpretedBool pat
            ForallPattern _ -> translateUninterpretedBool pat
            InPattern _ -> translateUninterpretedBool pat

            -- Invalid: no translation, should not occur in predicates
            ApplicationPattern _ -> empty
            DomainValuePattern _ -> empty
            NextPattern _ -> empty
            RewritesPattern _ -> empty
            VariablePattern _ -> empty

    translatePredicateAnd And { andFirst, andSecond } =
        SMT.and
            <$> translatePredicatePattern andFirst
            <*> translatePredicatePattern andSecond

    translatePredicateEquals
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        SMT.eq
            <$> translatePredicateEqualsChild equalsFirst
            <*> translatePredicateEqualsChild equalsSecond
      where
        translatePredicateEqualsChild
          | equalsOperandSort == equalsResultSort =
            -- Child patterns are predicates.
            translatePredicatePattern
          | otherwise =
            translatePattern equalsOperandSort

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
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        )
    => p
    -> Translator p SExpr
translateInt pat =
    case Functor.Foldable.project pat of
        VariablePattern _ -> translateUninterpreted SMT.tInt pat
        DomainValuePattern dv ->
            (return . SMT.int . Builtin.runParser ctx)
                (Builtin.parseDomainValue Builtin.Int.parse dv)
          where
            ctx = Text.unpack Builtin.Int.sort
        ApplicationPattern app ->
            translateApplication app
        _ -> empty

-- | Translate a functional pattern in the builtin Bool sort for SMT.
translateBool
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        )
    => p
    -> Translator p SExpr
translateBool pat =
    case Functor.Foldable.project pat of
        VariablePattern _ -> translateUninterpreted SMT.tBool pat
        DomainValuePattern dv ->
            (return . SMT.bool . Builtin.runParser ctx)
            (Builtin.parseDomainValue Builtin.Bool.parse dv)
            where
            ctx = Text.unpack Builtin.Bool.sort
        NotPattern Not { notChild } ->
            -- \not is equivalent to BOOL.not for functional patterns.
            -- The following is safe because non-functional patterns will fail
            -- to translate.
            SMT.not <$> translateBool notChild
        ApplicationPattern app ->
            translateApplication app
        _ -> empty

translateApplication
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        )
    => Application Object p
    -> Translator p SExpr
translateApplication
    Application
        { applicationSymbolOrAlias
        , applicationChildren
        }
    =
    case getSmtlib (symAttributes smtTools applicationSymbolOrAlias) of
        Nothing -> empty
        Just sExpr ->
            applySExpr sExpr
                <$> zipWithM translatePattern
                    applicationChildrenSorts
                    applicationChildren
    where
    smtTools :: MetadataTools Object Smtlib
    smtTools = StepperAttributes.smtlib <$> given

    applicationChildrenSorts =
        applicationSortsOperands
        $ symbolOrAliasSorts smtTools applicationSymbolOrAlias

translatePattern
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        )
    => Sort Object
    -> p
    -> Translator p SExpr
translatePattern sort =
    case getHook (sortAttributes hookTools sort) of
        Just builtinSort
          | builtinSort == Builtin.Bool.sort -> translateBool
          | builtinSort == Builtin.Int.sort -> translateInt
        _ -> const empty
  where
    hookTools :: MetadataTools Object Hook
    hookTools = StepperAttributes.hook <$> given
