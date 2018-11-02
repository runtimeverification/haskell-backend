{-|
Module      : Data.Kore.SMT.SMT
Description : Basic SMT interface.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.SMT.SMT
    ( unsafeTryRefutePredicate
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT, runMaybeT )
import           Control.Monad.Except
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as Monad.State
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
                 ( Given (..) )
import           Data.SBV as SMT
import qualified Data.Text as Text
import           GHC.IO.Unsafe
import           Prelude hiding
                 ( and, not, or )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Builtin as Builtin
import           Kore.Builtin.Hook
import qualified Kore.Builtin.Int as Builtin.Int
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Kore
import           Kore.SMT.Config
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes

data TranslationVariables var =
    TranslationVariables
        { boolVariables :: Map (PureMLPattern Object var) SBool
        , intVariables :: Map (PureMLPattern Object var) SInteger
        }

emptyTranslationVariables :: TranslationVariables variable
emptyTranslationVariables =
    TranslationVariables
        { boolVariables = Map.empty
        , intVariables = Map.empty
        }

lookupBoolPattern
    :: (Monad m, MonadPlus m, Ord (variable Object))
    => PureMLPattern Object variable
    -> StateT (TranslationVariables variable) m SBool
lookupBoolPattern pat =
    maybe empty return =<< Monad.State.gets (Map.lookup pat . boolVariables)

lookupIntPattern
    :: (Monad m, MonadPlus m, Ord (variable Object))
    => PureMLPattern Object variable
    -> StateT (TranslationVariables variable) m SInteger
lookupIntPattern pat =
    maybe empty return =<< Monad.State.gets (Map.lookup pat . intVariables)

freeBoolVariableFor
    ::  ( Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> StateT s (MaybeT Symbolic) SBool
freeBoolVariableFor pat = do
    var <- liftSMT SMT.free_
    Monad.State.modify' (insertBoolVariable pat var)
    return var

insertBoolVariable
    :: Ord (var Object)
    => PureMLPattern Object var
    -> SBool
    -> TranslationVariables var
    -> TranslationVariables var
insertBoolVariable pat var tvs@TranslationVariables { boolVariables } =
    tvs { boolVariables = Map.insert pat var boolVariables }

translateUninterpretedBool
    :: Ord (variable Object)
    => PureMLPattern Object variable
    -> StateT (TranslationVariables variable) (MaybeT Symbolic) SBool
translateUninterpretedBool pat =
    lookupBoolPattern pat <|> freeBoolVariableFor pat

freeIntVariableFor
    ::  ( Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> StateT s (MaybeT Symbolic) SInteger
freeIntVariableFor pat = do
    var <- liftSMT SMT.free_
    Monad.State.modify' (insertIntVariable pat var)
    return var

insertIntVariable
    :: Ord (var Object)
    => PureMLPattern Object var
    -> SInteger
    -> TranslationVariables var
    -> TranslationVariables var
insertIntVariable pat var tvs@TranslationVariables { intVariables } =
    tvs { intVariables = Map.insert pat var intVariables }

translateUninterpretedInt
    :: Ord (variable Object)
    => PureMLPattern Object variable
    -> StateT (TranslationVariables variable) (MaybeT Symbolic) SInteger
translateUninterpretedInt pat =
    lookupIntPattern pat <|> freeIntVariableFor pat

liftSMT :: Symbolic a -> StateT s (MaybeT Symbolic) a
liftSMT = Monad.Trans.lift . Monad.Trans.lift

config :: SMTConfig
config = z3

unsafeTryRefutePredicate
    :: forall level variable .
       ( Given (MetadataTools level StepperAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , SortedVariable variable
       )
    => SMTTimeOut
    -> Kore.Predicate level variable
    -> Maybe Bool
{-# NOINLINE unsafeTryRefutePredicate #-} -- Needed by: unsafePerformIO
unsafeTryRefutePredicate (SMTTimeOut timeout) p =
  case isMetaOrObject (Proxy :: Proxy level) of
    IsMeta   -> Nothing
    IsObject ->
        unsafePerformIO $ do
            let smtPredicate = do
                    setTimeOut timeout
                    smt <- runMaybeT (translatePredicate p)
                    case smt of
                        Nothing -> sBool "TranslationFailed"
                        Just p' -> return $ bnot p'
            res <- proveWith config smtPredicate
            return $ case res of
                ThmResult (Satisfiable   _ _) -> Nothing
                ThmResult (Unsatisfiable _ _) -> Just False
                _ -> Nothing

translatePredicate
    :: forall variable.
       (Ord (variable Object), Given (MetadataTools Object StepperAttributes))
    => Kore.Predicate Object variable
    -> MaybeT Symbolic SBool
translatePredicate predicate =
    evalStateT
        (translatePredicatePattern $ Kore.unwrapPredicate predicate)
        emptyTranslationVariables
  where
    translatePredicatePattern
        :: s ~ TranslationVariables variable
        => PureMLPattern Object variable
        -> StateT s (MaybeT Symbolic) SBool
    translatePredicatePattern pat =
        case Functor.Foldable.project pat of
            -- Logical connectives: translate as connectives
            AndPattern and -> translatePredicateAnd and
            BottomPattern _ -> return SMT.false
            EqualsPattern eq ->
                -- Equality of predicates and builtins can be translated to
                -- equality in the SMT solver, but other patterns must remain
                -- uninterpreted.
                translatePredicateEquals eq <|> translateUninterpretedBool pat
            IffPattern iff -> translatePredicateIff iff
            ImpliesPattern implies -> translatePredicateImplies implies
            NotPattern not -> translatePredicateNot not
            OrPattern or -> translatePredicateOr or
            TopPattern _ -> return SMT.true

            -- Uninterpreted: translate as variables
            ApplicationPattern _ -> translateUninterpretedBool pat
            CeilPattern _ -> translateUninterpretedBool pat
            ExistsPattern _ -> translateUninterpretedBool pat
            FloorPattern _ -> translateUninterpretedBool pat
            ForallPattern _ -> translateUninterpretedBool pat
            InPattern _ -> translateUninterpretedBool pat

            -- Invalid: no translation, should not occur in predicates
            DomainValuePattern _ -> empty
            NextPattern _ -> empty
            RewritesPattern _ -> empty
            VariablePattern _ -> empty

    hookTools :: MetadataTools Object Hook
    hookTools = StepperAttributes.hook <$> given

    translatePredicateAnd And { andFirst, andSecond } =
        (SMT.&&&)
            <$> translatePredicatePattern andFirst
            <*> translatePredicatePattern andSecond

    translatePredicateEquals
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      | equalsOperandSort == equalsResultSort =
        -- Child patterns are predicates.
        translatePredicateEqualsPredicate
      | otherwise =
        case getHook (sortAttributes hookTools equalsOperandSort) of
            Nothing -> empty
            Just builtinSort ->
                -- Child patterns are hooked to builtins that may be
                -- translatable to SMT theories.
                translatePredicateEqualsBuiltin builtinSort
      where
        translatePredicateEqualsPredicate =
            (SMT.<=>)
                <$> translatePredicatePattern equalsFirst
                <*> translatePredicatePattern equalsSecond
        translatePredicateEqualsBuiltin builtinSort
          | builtinSort == Builtin.Bool.sort =
            translateEqualsBool equalsFirst equalsSecond
          | builtinSort == Builtin.Int.sort =
            translateEqualsInt equalsFirst equalsSecond
          | otherwise = empty

    translatePredicateIff Iff { iffFirst, iffSecond } =
        (SMT.<=>)
            <$> translatePredicatePattern iffFirst
            <*> translatePredicatePattern iffSecond

    translatePredicateImplies Implies { impliesFirst, impliesSecond } =
        (SMT.==>)
            <$> translatePredicatePattern impliesFirst
            <*> translatePredicatePattern impliesSecond

    translatePredicateNot Not { notChild } =
        SMT.bnot <$> translatePredicatePattern notChild

    translatePredicateOr Or { orFirst, orSecond } =
        (SMT.|||)
            <$> translatePredicatePattern orFirst
            <*> translatePredicatePattern orSecond

translateEqualsInt
    :: forall p s variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> p
    -> StateT s (MaybeT Symbolic) SBool
translateEqualsInt first second =
    (SMT..==) <$> translateInt first <*> translateInt second

translateInt
    :: forall p s variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> StateT s (MaybeT Symbolic) SInteger
translateInt pat =
    case Functor.Foldable.project pat of
        VariablePattern _ -> translateUninterpretedInt pat
        DomainValuePattern dv ->
            (return . SMT.literal . Builtin.runParser ctx)
            (Builtin.parseDomainValue Builtin.Int.parse dv)
            where
            ctx = Text.unpack Builtin.Int.sort
        ApplicationPattern app ->
            translateApplication app
        _ -> empty
  where
    hookTools :: MetadataTools Object Hook
    hookTools = StepperAttributes.hook <$> given

    translateApplication
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
      =
        case getHook (symAttributes hookTools applicationSymbolOrAlias) of
            Nothing -> empty
            Just hook ->
                case hook of
                    "INT.min" -> binaryOp SMT.smin
                    "INT.max" -> binaryOp SMT.smax
                    "INT.add" -> binaryOp (+)
                    "INT.sub" -> binaryOp (-)
                    "INT.mul" -> binaryOp (*)
                    "INT.tdiv" -> binaryOp sQuot
                    "INT.tmod" -> binaryOp sRem
                    "INT.and" -> binaryOp (.&.)
                    "INT.or" -> binaryOp (.|.)
                    "INT.xor" -> binaryOp xor
                    "INT.not" -> unaryOp complement
                    _ -> empty
              where
                ctx = Text.unpack hook
                unaryOp op =
                    case applicationChildren of
                        [first] ->
                            op <$> translateInt first
                        _ ->
                            Builtin.wrongArity ctx
                binaryOp op =
                    case applicationChildren of
                        [first, second] ->
                            op <$> translateInt first <*> translateInt second
                        _ ->
                            Builtin.wrongArity ctx

translateEqualsBool
    :: forall p s variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> p
    -> StateT s (MaybeT Symbolic) SBool
translateEqualsBool first second =
    (SMT..==) <$> translateBool first <*> translateBool second

translateBool
    :: forall p s variable.
        ( Given (MetadataTools Object StepperAttributes)
        , Ord (variable Object)
        , p ~ PureMLPattern Object variable
        , s ~ TranslationVariables variable
        )
    => p
    -> StateT s (MaybeT Symbolic) SBool
translateBool pat =
    case Functor.Foldable.project pat of
        VariablePattern _ -> translateUninterpretedBool pat
        DomainValuePattern dv ->
            (return . SMT.literal . Builtin.runParser ctx)
            (Builtin.parseDomainValue Builtin.Bool.parse dv)
            where
            ctx = Text.unpack Builtin.Bool.sort
        NotPattern Not { notChild } ->
            -- \not is equivalent to BOOL.not for functional patterns.
            -- The following is safe because non-functional patterns will fail
            -- to translate.
            SMT.bnot <$> translateBool notChild
        ApplicationPattern app ->
            translateApplication app
        _ -> empty
  where
    hookTools :: MetadataTools Object Hook
    hookTools = StepperAttributes.hook <$> given

    translateApplication
        Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
      =
        case getHook (symAttributes hookTools applicationSymbolOrAlias) of
            Nothing -> empty
            Just hook ->
                case hook of
                    "INT.gt" -> binaryIntOp (SMT..>)
                    "INT.ge" -> binaryIntOp (SMT..>=)
                    "INT.eq" -> binaryIntOp (SMT..==)
                    "INT.le" -> binaryIntOp (SMT..<=)
                    "INT.lt" -> binaryIntOp (SMT..<)
                    "INT.ne" -> binaryIntOp (SMT../=)

                    "BOOL.or" -> binaryOp (SMT.|||)
                    "BOOL.and" -> binaryOp (SMT.&&&)
                    "BOOL.xor" -> binaryOp (SMT.<+>)
                    "BOOL.ne" -> binaryOp (SMT../=)
                    "BOOL.eq" -> binaryOp (SMT.<=>)
                    "BOOL.not" -> unaryOp SMT.bnot
                    "BOOL.implies" -> binaryOp (SMT.==>)
                    _ -> empty
              where
                ctx = Text.unpack hook
                unaryOp op =
                    case applicationChildren of
                        [first] ->
                            op <$> translateBool first
                        _ ->
                            Builtin.wrongArity ctx
                binaryOp op =
                    case applicationChildren of
                        [first, second] ->
                            op <$> translateBool first <*> translateBool second
                        _ ->
                            Builtin.wrongArity ctx
                binaryIntOp op =
                    case applicationChildren of
                        [first, second] ->
                            op <$> translateInt first <*> translateInt second
                        _ ->
                            Builtin.wrongArity ctx
