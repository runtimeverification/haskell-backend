{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluate
    , refutePredicate
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Error
                 ( MaybeT, runMaybeT )
import           Control.Monad.Counter
                 ( CounterT, evalCounterT )
import qualified Control.Monad.Counter as Counter
import           Control.Monad.Except
import           Control.Monad.Morph as Morph
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as State
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
import           Kore.Attribute.Smtlib
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Builtin.Int
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier (..) )
import           Kore.Step.StepperAttributes
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Unparser
import           SMT
                 ( MonadSMT, Result (..), SExpr (..), SMT )
import qualified SMT

{- | Attempt to evaluate a predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall level variable .
        ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , Given (MetadataTools level StepperAttributes)
        )
    => PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> Predicate level variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution level variable, SimplificationProof level)
evaluate
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (simplified, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    refute <-
        case () of
            _ | OrOfExpandedPattern.isTrue simplified -> return (Just True)
              | OrOfExpandedPattern.isFalse simplified -> return (Just False)
              | otherwise -> refutePredicate predicate
    let simplified' =
            case refute of
                Just False -> ExpandedPattern.bottom
                _ -> OrOfExpandedPattern.toExpandedPattern simplified
        (subst, _proof) = asPredicateSubstitution simplified'
    return (subst, SimplificationProof)

asPredicateSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> (PredicateSubstitution level variable, SimplificationProof level)
asPredicateSubstitution
    Predicated {term, predicate, substitution}
  =
    let
        andPatt = makeAndPredicate predicate (wrapPredicate term)
    in
        ( Predicated
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )

{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.

 -}
refutePredicate
    :: forall level variable m.
       ( Given (MetadataTools level StepperAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , SortedVariable variable
       , MonadSMT m
       )
    => Predicate level variable
    -> m (Maybe Bool)
refutePredicate korePredicate =
    case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta   -> return Nothing
        IsObject ->
            SMT.inNewScope $ runMaybeT $ do
                smtPredicate <- translatePredicate korePredicate
                SMT.assert smtPredicate
                result <- SMT.check
                case result of
                    Unsat -> return False
                    _ -> empty

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
    :: forall variable.
        (Ord (variable Object), Given (MetadataTools Object StepperAttributes))
    => Predicate Object variable
    -> MaybeT SMT SExpr
translatePredicate predicate = do
    let translator = translatePredicatePattern $ unwrapPredicate predicate
    runTranslator translator
  where
    translatePredicatePattern
        :: StepPattern Object variable
        -> Translator (StepPattern Object variable) SExpr
    translatePredicatePattern pat =
        case Cofree.tailF (Recursive.project pat) of
            -- Logical connectives: translate as connectives
            AndPattern and' -> translatePredicateAnd and'
            BottomPattern _ -> return (SMT.bool False)
            EqualsPattern eq ->
                -- Equality of predicates and builtins can be translated to
                -- equality in the SMT solver, but other patterns must remain
                -- uninterpreted.
                translatePredicateEquals eq <|> translateUninterpretedBool pat
            IffPattern iff -> translatePredicateIff iff
            ImpliesPattern implies -> translatePredicateImplies implies
            NotPattern not' -> translatePredicateNot not'
            OrPattern or' -> translatePredicateOr or'
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
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ StepPattern Object variable
        )
    => p
    -> Translator p SExpr
translateInt pat =
    case Cofree.tailF (Recursive.project pat) of
        VariablePattern _ -> translateUninterpretedInt pat
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
        , p ~ StepPattern Object variable
        )
    => p
    -> Translator p SExpr
translateBool pat =
    case Cofree.tailF (Recursive.project pat) of
        VariablePattern _ -> translateUninterpretedBool pat
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
        , p ~ StepPattern Object variable
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

    applicationChildrenSorts = getSort <$> applicationChildren

translatePattern
    :: forall p variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ StepPattern Object variable
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

-- ----------------------------------------------------------------
-- Translator

type Translator p = MaybeT (StateT (Map p SExpr) (CounterT SMT))

runTranslator :: Ord p => Translator p a -> MaybeT SMT a
runTranslator = Morph.hoist (evalCounterT . flip evalStateT Map.empty)

translateUninterpreted
    :: Ord p
    => SExpr  -- ^ type name
    -> p  -- ^ uninterpreted pattern
    -> Translator p SExpr
translateUninterpreted t pat =
    lookupPattern <|> freeVariable
  where
    lookupPattern = do
        result <- State.gets $ Map.lookup pat
        maybe empty return result
    freeVariable = do
        n <- Counter.increment
        var <- SMT.declare ("<" <> Text.pack (show n) <> ">") t
        State.modify' (Map.insert pat var)
        return var

translateUninterpretedBool
    :: Ord p
    => p  -- ^ uninterpreted pattern
    -> Translator p SExpr
translateUninterpretedBool = translateUninterpreted SMT.tBool

translateUninterpretedInt
    :: Ord p
    => p  -- ^ uninterpreted pattern
    -> Translator p SExpr
translateUninterpretedInt = translateUninterpreted SMT.tInt
