{-|
Module      : Kore.SMT.Translator
Description : Context for translating predicates to SMT
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.SMT.Translator
    ( Translator
    , runTranslator
    , translateUninterpreted
    , translateUninterpretedBool
    , translateUninterpretedInt
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Control.Monad.Counter
                 ( CounterT, evalCounterT )
import qualified Control.Monad.Counter as Monad.Counter
import           Control.Monad.Except
import qualified Control.Monad.Morph as Morph
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as Monad.State
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Prelude hiding
                 ( and, not, or )

import           SMT
                 ( MonadSMT (..), SExpr (..), SMT )
import qualified SMT

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
        result <- Monad.State.gets $ Map.lookup pat
        maybe empty return result
    freeVariable = do
        n <- Monad.Counter.increment
        var <- liftSMT $ SMT.declare ("<" ++ show n ++ ">") t
        Monad.State.modify' (Map.insert pat var)
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
