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
    , Builtin.sortDeclVerifier
    , Builtin.symbolVerifier
    , Builtin.verifyDomainValue
    , koreVerifiers
    , koreEvaluators
    , evaluators
    , externalizePattern
    , asMetaPattern
    ) where

import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )
import           Data.Text
                 ( Text )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Pure
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Hook
                 ( Hook (..) )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import           Kore.Builtin.Error
                 ( notImplementedInternal )
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Builtin.Krypto as Krypto
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import qualified Kore.Builtin.String as String
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), VerifiedModule )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Pattern

{- | The default type of builtin domain values.
 -}
type Builtin = DomainValue Object Domain.Builtin (CommonStepPattern Object)

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
    -> Map (AxiomIdentifier Object) Builtin.Function
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
    -> Map (AxiomIdentifier Object) Builtin.Function
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
        -> Map (Id Object) StepperAttributes
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
        -> Map (Id Object) StepperAttributes
    importHookedSymbolAttributes (_, _, im) = hookedSymbolAttributes im

    lookupBuiltins :: StepperAttributes -> Maybe Builtin.Function
    lookupBuiltins Attribute.Symbol { Attribute.hook = Hook { getHook } } =
        do
            name <- getHook
            impl <- Map.lookup name builtins
            pure impl

{- | Externalize all builtin domain values in the given pattern.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'

 -}
-- TODO (thomas.tuegel): Transform from Domain.Internal to Domain.External.
externalizePattern
    ::  forall variable. Ord (variable Object)
    =>  StepPattern Object variable
    ->  StepPattern Object variable
externalizePattern =
    Recursive.unfold externalizePatternWorker
  where
    externalizePatternWorker
        ::  StepPattern Object variable
        ->  Base (StepPattern Object variable) (StepPattern Object variable)
    externalizePatternWorker (Recursive.project -> original@(_ :< pat)) =
        case pat of
            DomainValuePattern domain ->
                case domain of
                    Domain.BuiltinExternal _ -> original
                    Domain.BuiltinMap  builtin ->
                        Recursive.project (Map.asPattern builtin)
                    Domain.BuiltinList builtin ->
                        Recursive.project (List.asPattern builtin)
                    Domain.BuiltinSet  builtin ->
                        Recursive.project (Set.asPattern builtin)
                    Domain.BuiltinInt  builtin ->
                        Recursive.project (Int.asPattern builtin)
                    Domain.BuiltinBool builtin ->
                        Recursive.project (Bool.asPattern builtin)
            _ -> original

{- | Extract the meta-level pattern argument of a domain value.

WARNING: This is not implemented for internal domain values. Use
'externalizePattern' before calling this function.

 -}
asMetaPattern
    :: Functor domain
    => Domain.Builtin child
    -> PurePattern Meta domain Variable (Annotation.Null Meta)
asMetaPattern =
    \case
        Domain.BuiltinExternal ext ->
            castVoidDomainValues domainValueChild
          where
            Domain.External { domainValueChild } = ext
        Domain.BuiltinMap _ -> notImplementedInternal
        Domain.BuiltinList _ -> notImplementedInternal
        Domain.BuiltinSet _ -> notImplementedInternal
        Domain.BuiltinInt _ -> notImplementedInternal
        Domain.BuiltinBool _ -> notImplementedInternal
