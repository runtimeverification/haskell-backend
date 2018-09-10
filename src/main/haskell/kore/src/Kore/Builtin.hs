{- |
Module      : Kore.Builtin
Description : Built-in sorts and symbols
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified.

@
    import qualified Kore.Builtin as Builtin
@
 -}
module Kore.Builtin
    ( Builtin.Verifiers (..)
    , Builtin.PatternVerifier (..)
    , Builtin.Function
    , Builtin.sortDeclVerifier
    , Builtin.symbolVerifier
    , koreVerifiers
    , koreEvaluators
    , evaluators
    ) where

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Hook as Hook
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Builtin.Map as Map
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), KoreIndexedModule )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )

{- | Verifiers for Kore builtin sorts.

  If you aren't sure which verifiers you need, use these.

 -}
koreVerifiers :: Builtin.Verifiers
koreVerifiers =
    Builtin.Verifiers
    { sortDeclVerifiers =
           Bool.sortDeclVerifiers
        <> Int.sortDeclVerifiers
        <> Map.sortDeclVerifiers
    , symbolVerifiers =
           Bool.symbolVerifiers
        <> Int.symbolVerifiers
        <> Map.symbolVerifiers
        <> KEqual.symbolVerifiers
    , patternVerifier =
           Bool.patternVerifier
        <> Int.patternVerifier
    }

{- | Construct an evaluation context for Kore builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step'

 -}
koreEvaluators
    :: KoreIndexedModule StepperAttributes
    -- ^ Module under which evaluation takes place
    -> Map (Kore.Id Object) [Builtin.Function]
koreEvaluators = evaluators builtins
  where
    builtins :: Map String Builtin.Function
    builtins =
        Map.unions
            [ Bool.builtinFunctions
            , Int.builtinFunctions
            , KEqual.builtinFunctions
            , Map.builtinFunctions
            ]

{- | Construct an evaluation context for the given builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step', 'koreEvaluators'

 -}
evaluators
    :: Map String Builtin.Function
    -- ^ Builtin functions indexed by name
    -> KoreIndexedModule StepperAttributes
    -- ^ Module under which evaluation takes place
    -> Map (Kore.Id Object) [Builtin.Function]
evaluators builtins indexedModule =
    Map.mapMaybe lookupBuiltins (hookedSymbolAttributes indexedModule)
  where
    hookedSymbolAttributes
        :: KoreIndexedModule StepperAttributes
        -> Map (Kore.Id Object) StepperAttributes
    hookedSymbolAttributes im =
        Map.union
            (justAttributes <$> IndexedModule.hookedObjectSymbolSentences im)
            (Map.unions (importHookedSymbolAttributes <$> indexedModuleImports im))
      where
        justAttributes (attrs, _) = attrs

    importHookedSymbolAttributes
        :: (a, b, KoreIndexedModule StepperAttributes)
        -> Map (Kore.Id Object) StepperAttributes
    importHookedSymbolAttributes (_, _, im) = hookedSymbolAttributes im

    lookupBuiltins :: StepperAttributes -> Maybe [Builtin.Function]
    lookupBuiltins StepperAttributes { hook } =
        do
            name <- Hook.getHook hook
            impl <- Map.lookup name builtins
            pure [impl]
