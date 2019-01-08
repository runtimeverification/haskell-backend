{- |
Module      : Kore.Builtin.Krypto
Description : Built-in cryptographic functions.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Krypto as Krypto
@
 -}

module Kore.Builtin.Krypto
    ( symbolVerifiers
    , builtinFunctions
    , keccakKey
    , keccakKeyT
    ) where

import           Crypto.Hash
                 ( Digest, Keccak_256, hash )
import           Data.ByteString.Char8
                 ( pack )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Text
                 ( Text )

import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.String as String
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Sort
                 ( Sort )
import           Kore.Step.Function.Data
                 ( AttemptedFunction )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

keccakKey :: String
keccakKey = "KRYPTO.keccak256"
keccakKeyT :: Text
keccakKeyT = "KRYPTO.keccak256"

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( keccakKeyT
      , Builtin.verifySymbol String.assertSort [String.assertSort]
      )
    ]

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (keccakKeyT, evalKeccak)
        ]

evalKeccak :: Builtin.Function
evalKeccak =
    Builtin.functionEvaluator evalKeccak0
  where
    evalKeccak0
        :: (Ord (variable Object), Show (variable Object))
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalKeccak0 _ _ resultSort arguments =
        Builtin.getAttemptedFunction $ do
            let
                arg =
                    case arguments of
                      [input] -> input
                      _ -> Builtin.wrongArity keccakKey
            str <- String.expectBuiltinString keccakKey arg
            let
                digest = hash . pack $ str :: Digest Keccak_256
                result = show digest
            Builtin.appliedFunction
                $ String.asExpandedPattern resultSort result
