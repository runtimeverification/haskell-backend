{-|
Module      : Kore.SMT.Translator
Description : Context for translating predicates to SMT
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.SMT.Translator
    ( Translator
    , runTranslator
    , translateUninterpretedBool
    , translateUninterpretedInt
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Control.Lens
                 ( Lens' )
import qualified Control.Lens as Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as Monad.State
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.SBV as SMT
import           Prelude hiding
                 ( and, not, or )

data TranslationState p =
    TranslationState
        { _boolVariables :: !(Map p SBool)
        , _intVariables :: !(Map p SInteger)
        }

Lens.makeLenses ''TranslationState

type Translator p = StateT (TranslationState p) (MaybeT Symbolic)

liftSymbolic :: Symbolic a -> Translator p a
liftSymbolic symb = (Monad.Trans.lift (Monad.Trans.lift symb))

runTranslator :: Translator p a -> MaybeT Symbolic a
runTranslator translator =
    evalStateT translator emptyTranslationState
  where
    emptyTranslationState :: TranslationState p
    emptyTranslationState =
        TranslationState
            { _boolVariables = Map.empty
            , _intVariables = Map.empty
            }

translateUninterpreted
    :: (Ord p, SymWord a)
    => Lens' (TranslationState p) (Map p (SBV a))
    -> p
    -> Translator p (SBV a)
translateUninterpreted lens pat =
    lookupPattern <|> freeVariable
  where
    lookupPattern = do
        result <- Lens.zoom lens $ Monad.State.gets $ Map.lookup pat
        maybe empty return result
    freeVariable = do
        var <- liftSymbolic SMT.free_
        Lens.zoom lens $ Monad.State.modify' (Map.insert pat var)
        return var

translateUninterpretedBool :: Ord p => p -> Translator p SBool
translateUninterpretedBool = translateUninterpreted boolVariables

translateUninterpretedInt :: Ord p => p -> Translator p SInteger
translateUninterpretedInt = translateUninterpreted intVariables
