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
    ) where

import qualified Data.Functor.Foldable as Recursive
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )
import           Data.Text
                 ( Text )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Pure
import           Kore.AST.Valid
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
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), VerifiedModule )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes )
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
    , patternVerifier =
           Bool.patternVerifier
        <> Int.patternVerifier
        <> String.patternVerifier
    }

{- | Construct an evaluation context for Kore builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step'

 -}
koreEvaluators
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ Module under which evaluation takes place
    -> Map (Id Object) Builtin.Function
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
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ Module under which evaluation takes place
    -> Map (Id Object) Builtin.Function
evaluators builtins indexedModule =
    Map.mapMaybe lookupBuiltins (hookedSymbolAttributes indexedModule)
  where
    hookedSymbolAttributes
        :: VerifiedModule StepperAttributes AxiomPatternAttributes
        -> Map (Id Object) StepperAttributes
    hookedSymbolAttributes im =
        Map.union
            (justAttributes <$> IndexedModule.hookedObjectSymbolSentences im)
            (Map.unions (importHookedSymbolAttributes <$> indexedModuleImports im))
      where
        justAttributes (attrs, _) = attrs

    importHookedSymbolAttributes
        :: (a, b, VerifiedModule StepperAttributes AxiomPatternAttributes)
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
    :: VerifiedModule declAttrs axiomAttrs
    -- ^ indexed module defining hooks for builtin domains
    -> Builtin
    -- ^ domain value
    -> Either (Error e) (CommonStepPattern Object)
asPattern
    indexedModule
    DomainValue { domainValueSort, domainValueChild }
  =
    case domainValueChild of
        Domain.BuiltinPattern _ ->
            return (mkDomainValue domainValueSort domainValueChild)
        Domain.BuiltinMap map' ->
            Map.asPattern indexedModule domainValueSort <*> pure map'
        Domain.BuiltinList list ->
            List.asPattern indexedModule domainValueSort <*> pure list
        Domain.BuiltinSet set ->
            Set.asPattern indexedModule domainValueSort <*> pure set

{- | Externalize all builtin domain values in the given pattern.

    All builtins will be rendered using their concrete Kore syntax. The given
    indexed module must define the appropriate hooks.

    See also: 'asPattern'

 -}
-- TODO (thomas.tuegel): Transform from Domain.Builtin to Domain.External.
externalizePattern
    :: VerifiedModule declAttrs axiomAttrs
    -- ^ indexed module defining hooks for builtin domains
    -> CommonStepPattern Object
    -> Either (Error e) (CommonStepPattern Object)
externalizePattern indexedModule =
    Recursive.fold externalizePatternWorker
  where
    externalizePatternWorker (ann :< pat) =
        case pat of
            DomainValuePattern dv ->
                asPattern indexedModule =<< sequence dv
            _ -> Recursive.embed . (ann :<) <$> sequence pat

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
