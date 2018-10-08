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
    , Builtin
    , Builtin.sortDeclVerifier
    , Builtin.symbolVerifier
    , koreVerifiers
    , koreEvaluators
    , evaluators
    , asPattern
    , externalizePattern
    , asMetaPattern
    -- * Errors
    , notImplementedInternal
    ) where

import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )
import           GHC.Stack
                 ( HasCallStack )

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Meta, Object )
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Hook as Hook
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), KoreIndexedModule )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )

{- | The default type of builtin domain values.
 -}
type Builtin =
    Kore.DomainValue Object (Kore.BuiltinDomain (Kore.CommonPurePattern Object))

{- | Verifiers for Kore builtin sorts.

  If you aren't sure which verifiers you need, use these.

 -}
koreVerifiers :: Builtin.Verifiers
koreVerifiers =
    Builtin.Verifiers
    { sortDeclVerifiers =
           Bool.sortDeclVerifiers
        <> Int.sortDeclVerifiers
        <> List.sortDeclVerifiers
        <> Map.sortDeclVerifiers
        <> Set.sortDeclVerifiers
    , symbolVerifiers =
           Bool.symbolVerifiers
        <> Int.symbolVerifiers
        <> List.symbolVerifiers
        <> Map.symbolVerifiers
        <> KEqual.symbolVerifiers
        <> Set.symbolVerifiers
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

{- | Represent a 'Builtin' domain value as an object-level pattern.

    Any builtins with an internal representation are externalized to their
    concrete Kore syntax. The given indexed module must define the appropriate
    hooks.

 -}
asPattern
    :: KoreIndexedModule attrs
    -- ^ indexed module defining hooks for builtin domains
    -> Builtin
    -- ^ domain value
    -> Either (Error e) (Kore.CommonPurePattern Object)
asPattern
    indexedModule
    Kore.DomainValue { domainValueSort, domainValueChild }
  =
    case domainValueChild of
        Kore.BuiltinDomainPattern _ ->
            return (Kore.DV_ domainValueSort domainValueChild)
        Kore.BuiltinDomainMap map' ->
            Map.asPattern indexedModule domainValueSort <*> pure map'
        Kore.BuiltinDomainList list ->
            List.asPattern indexedModule domainValueSort <*> pure list
        Kore.BuiltinDomainSet set ->
            Set.asPattern indexedModule domainValueSort <*> pure set

{- | Externalize all builtin domain values in the given pattern.

    All builtins will be rendered using their concrete Kore syntax. The given
    indexed module must define the appropriate hooks.

    See also: 'asPattern'

 -}
-- TODO (thomas.tuegel): Parameterize patterns on the type of domain values. Use
-- 'StringLiteral' as the domain value type in the parser and a distinct domain
-- type for internally-represented builtin domains. Use this function to change
-- the domain value type parameter of the pattern and eliminate error cases
-- throughout.
externalizePattern
    :: KoreIndexedModule attrs
    -- ^ indexed module defining hooks for builtin domains
    -> Kore.CommonPurePattern Object
    -> Either (Error e) (Kore.CommonPurePattern Object)
externalizePattern indexedModule =
    Functor.Foldable.fold externalizePattern0
  where
    externalizePattern0 =
        \case
            Kore.DomainValuePattern dv ->
                asPattern indexedModule =<< traverse sequence dv
            pat -> Functor.Foldable.embed <$> sequence pat

{- | Extract the meta-level pattern argument of a domain value.

    WARNING: This is not implemented for internal domain values. Use
    'externalizePattern' before calling this function.

 -}
asMetaPattern
    :: Kore.BuiltinDomain child
    -> Kore.CommonPurePattern Meta
asMetaPattern =
    \case
        Kore.BuiltinDomainPattern pat -> pat
        Kore.BuiltinDomainMap _ -> notImplementedInternal
        Kore.BuiltinDomainList _ -> notImplementedInternal
        Kore.BuiltinDomainSet _ -> notImplementedInternal

{- | Throw an error for operations not implemented for internal domain values.
 -}
notImplementedInternal :: HasCallStack => a
notImplementedInternal = error "Not implemented for internal domain values"
