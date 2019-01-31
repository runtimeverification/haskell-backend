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
    ) where

import           Crypto.Hash
                 ( Digest, Keccak_256, hash )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.String
                 ( IsString, fromString )
import           Data.Text
                 ( Text )
import qualified Data.Text.Encoding as Text

import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.String as String
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Sort
                 ( Sort )
import           Kore.Step.Function.Data
                 ( AttemptedAxiom )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

keccakKey :: IsString s => s
keccakKey = "KRYPTO.keccak256"

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( keccakKey
      , Builtin.verifySymbol String.assertSort [String.assertSort]
      )
    ]

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (keccakKey, evalKeccak)
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
        -> Simplifier (AttemptedAxiom Object variable)
    evalKeccak0 _ _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let
                arg =
                    case arguments of
                      [input] -> input
                      _ -> Builtin.wrongArity keccakKey
            str <- String.expectBuiltinString keccakKey arg
            let
                digest = hash . Text.encodeUtf8 $ str :: Digest Keccak_256
                result = fromString (show digest)
            Builtin.appliedFunction
                $ String.asExpandedPattern resultSort result
