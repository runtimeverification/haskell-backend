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
    , Builtin.DomainValueVerifiers
    , Builtin.Function
    , Builtin
    , Builtin.SymbolVerifier (..)
    , Builtin.SortVerifier (..)
    , Builtin.sortDeclVerifier
    , Builtin.symbolVerifier
    , Builtin.verifyDomainValue
    , koreVerifiers
    , koreEvaluators
    , evaluators
    , externalize
    , internalize
    , renormalize
    ) where

import qualified Control.Lens as Lens
import Data.Function
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import qualified Data.HashMap.Strict as HashMap
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Semigroup
    ( (<>)
    )
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Hook
    ( Hook (..)
    )
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import Kore.Builtin.External
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Builtin.Krypto as Krypto
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import qualified Kore.Builtin.String as String
import Kore.IndexedModule.IndexedModule
    ( IndexedModule (..)
    , VerifiedModule
    )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.TermLike
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import Kore.Unparser
import Kore.Variables.Fresh

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
        <> String.sortDeclVerifiers
    , symbolVerifiers =
           Bool.symbolVerifiers
        <> Int.symbolVerifiers
        <> List.symbolVerifiers
        <> Map.symbolVerifiers
        <> KEqual.symbolVerifiers
        <> Set.symbolVerifiers
        <> String.symbolVerifiers
        <> Krypto.symbolVerifiers
    , domainValueVerifiers =
        HashMap.fromList
            [ (Bool.sort, Bool.patternVerifier)
            , (Int.sort, Int.patternVerifier)
            , (String.sort, String.patternVerifier)
            ]
    }

{- | Construct an evaluation context for Kore builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step'

 -}
koreEvaluators
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ Module under which evaluation takes place
    -> Map AxiomIdentifier Builtin.Function
koreEvaluators = evaluators builtins
  where
    builtins :: Map Text Builtin.Function
    builtins =
        Map.unions
            [ Bool.builtinFunctions
            , Int.builtinFunctions
            , KEqual.builtinFunctions
            , List.builtinFunctions
            , Map.builtinFunctions
            , Set.builtinFunctions
            , String.builtinFunctions
            , Krypto.builtinFunctions
            ]

{- | Construct an evaluation context for the given builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step', 'koreEvaluators'

 -}
evaluators
    :: Map Text Builtin.Function
    -- ^ Builtin functions indexed by name
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ Module under which evaluation takes place
    -> Map AxiomIdentifier Builtin.Function
evaluators builtins indexedModule =
    Map.mapMaybe
        lookupBuiltins
        (Map.mapKeys
            AxiomIdentifier.Application
            (hookedSymbolAttributes indexedModule)
        )
  where
    hookedSymbolAttributes
        :: VerifiedModule StepperAttributes Attribute.Axiom
        -> Map Id StepperAttributes
    hookedSymbolAttributes im =
        Map.union
            (justAttributes <$> IndexedModule.hookedObjectSymbolSentences im)
            (Map.unions
                (importHookedSymbolAttributes <$> indexedModuleImports im)
            )
      where
        justAttributes (attrs, _) = attrs

    importHookedSymbolAttributes
        :: (a, b, VerifiedModule StepperAttributes Attribute.Axiom)
        -> Map Id StepperAttributes
    importHookedSymbolAttributes (_, _, im) = hookedSymbolAttributes im

    lookupBuiltins :: StepperAttributes -> Maybe Builtin.Function
    lookupBuiltins Attribute.Symbol { Attribute.hook = Hook { getHook } } =
        do
            name <- getHook
            Map.lookup name builtins

{- | Convert a 'TermLike' to its internal representation.

@internalize@ modifies the term recursively from the bottom up, so any internal
representations are fully normalized.

 -}
internalize
    :: InternalVariable variable
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
internalize tools =
    Recursive.fold (internalize1 . Recursive.embed)
  where
    internalize1 =
            List.internalize tools
        .   Map.internalize tools
        .   Set.internalize tools

{- | Renormalize builtin types after substitution.
 -}
renormalize
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable -> TermLike variable
renormalize termLike =
    case termLike of
        BuiltinMap_ internalMap ->
            Lens.traverseOf (field @"builtinAcChild") Ac.renormalize internalMap
            & maybe bottom' mkBuiltinMap
        BuiltinSet_ internalSet ->
            Lens.traverseOf (field @"builtinAcChild") Ac.renormalize internalSet
            & maybe bottom' mkBuiltinSet
        _ -> termLike
  where
    bottom' = mkBottom (termLikeSort termLike)
