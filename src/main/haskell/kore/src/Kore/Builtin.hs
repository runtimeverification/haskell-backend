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
    , asPattern
    , externalizePattern
    , asMetaPattern
    ) where

import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Reflection as Reflection
import           Data.Semigroup
                 ( (<>) )
import           Data.Text
                 ( Text )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Hook
                 ( Hook (..) )
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
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, extractMetadataTools )
import           Kore.Step.Function.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Function.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )

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
    lookupBuiltins StepperAttributes { hook = Hook { getHook } } =
        do
            name <- getHook
            impl <- Map.lookup name builtins
            pure impl

{- | Represent a 'Builtin' domain value as an object-level pattern.

    Any builtins with an internal representation are externalized to their
    concrete Kore syntax. The given indexed module must define the appropriate
    hooks.

 -}
asPattern
    :: Given (MetadataTools Object StepperAttributes)
    => Builtin
    -- ^ domain value
    -> CommonStepPattern Object
asPattern DomainValue { domainValueSort, domainValueChild } =
    case domainValueChild of
        Domain.BuiltinPattern _ ->
            mkDomainValue domainValueSort domainValueChild
        Domain.BuiltinMap map' ->
            Map.asPattern domainValueSort map'
        Domain.BuiltinList list ->
            List.asPattern domainValueSort list
        Domain.BuiltinSet set ->
            Set.asPattern domainValueSort set
        Domain.BuiltinInteger int ->
            Int.asPattern domainValueSort int
        Domain.BuiltinBool bool ->
            Bool.asPattern domainValueSort bool


{- | Externalize all builtin domain values in the given pattern.

    All builtins will be rendered using their concrete Kore syntax. The given
    indexed module must define the appropriate hooks.

    See also: 'asPattern'

 -}
-- TODO (thomas.tuegel): Transform from Domain.Builtin to Domain.External.
externalizePattern
    :: VerifiedModule StepperAttributes axiomAttrs
    -- ^ indexed module defining hooks for builtin domains
    -> CommonStepPattern Object
    -> CommonStepPattern Object
externalizePattern indexedModule =
    Recursive.fold externalizePatternWorker
  where
    externalizePatternWorker
        ::  Base (CommonStepPattern Object) (CommonStepPattern Object)
        ->  CommonStepPattern Object
    externalizePatternWorker (ann :< pat) =
        case pat of
            DomainValuePattern dv -> Reflection.give tools asPattern dv
            _ -> Recursive.embed (ann :< pat)

    tools :: MetadataTools Object StepperAttributes
    tools = extractMetadataTools indexedModule

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
        Domain.BuiltinPattern pat -> castVoidDomainValues pat
        Domain.BuiltinMap _ -> notImplementedInternal
        Domain.BuiltinList _ -> notImplementedInternal
        Domain.BuiltinSet _ -> notImplementedInternal
        Domain.BuiltinInteger _ -> notImplementedInternal
        Domain.BuiltinBool _ -> notImplementedInternal
