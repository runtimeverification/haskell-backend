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
    , externalizePattern
    , internalize
    , renormalize
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Control.Lens as Lens
import           Data.Function
import qualified Data.Functor.Foldable as Recursive
import           Data.Generics.Product
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )
import           Data.Text
                 ( Text )
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Hook
                 ( Hook (..) )
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
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
                 ( SmtMetadataTools )
import qualified Kore.Internal.Alias as Alias
import qualified Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import qualified Kore.Syntax.Pattern as Syntax
import           Kore.Unparser
import           Kore.Variables.Fresh

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

{- | Externalize the 'TermLike' into a 'Syntax.Pattern'.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'

 -}
externalizePattern
    ::  forall variable
    .   (Ord variable, SortedVariable variable, Unparse variable)
    =>  TermLike variable
    ->  Syntax.Pattern variable Attribute.Null
externalizePattern =
    Recursive.unfold externalizePatternWorker
  where
    externalizePatternWorker
        ::  TermLike variable
        ->  Recursive.Base
                (Syntax.Pattern variable Attribute.Null)
                (TermLike variable)
    externalizePatternWorker termLike =
        case termLikeF of
            BuiltinF domain ->
                case domain of
                    Domain.BuiltinMap  builtin ->
                        (toPatternF . Recursive.project)
                            (Map.asTermLike builtin)
                    Domain.BuiltinList builtin ->
                        (toPatternF . Recursive.project)
                            (List.asTermLike builtin)
                    Domain.BuiltinSet  builtin ->
                        (toPatternF . Recursive.project)
                            (Set.asTermLike builtin)
                    Domain.BuiltinInt  builtin ->
                        (toPatternF . Recursive.project)
                            (Int.asTermLike builtin)
                    Domain.BuiltinBool builtin ->
                        (toPatternF . Recursive.project)
                            (Bool.asTermLike builtin)
                    Domain.BuiltinString builtin ->
                        (toPatternF . Recursive.project)
                            (String.asTermLike builtin)
            _ -> toPatternF termLikeBase
      where
        termLikeBase@(_ :< termLikeF) = Recursive.project termLike

    toPatternF
        :: GHC.HasCallStack
        => Recursive.Base (TermLike variable) (TermLike variable)
        -> Recursive.Base
            (Syntax.Pattern variable Attribute.Null)
            (TermLike variable)
    toPatternF (_ :< termLikeF) =
        (Attribute.Null :<)
        $ case termLikeF of
            AndF andF -> Syntax.AndF andF
            ApplyAliasF applyAliasF ->
                Syntax.ApplicationF
                $ mapHead Alias.toSymbolOrAlias applyAliasF
            ApplySymbolF applySymbolF ->
                Syntax.ApplicationF
                $ mapHead Symbol.toSymbolOrAlias applySymbolF
            BottomF bottomF -> Syntax.BottomF bottomF
            CeilF ceilF -> Syntax.CeilF ceilF
            DomainValueF domainValueF -> Syntax.DomainValueF domainValueF
            EqualsF equalsF -> Syntax.EqualsF equalsF
            ExistsF existsF -> Syntax.ExistsF existsF
            FloorF floorF -> Syntax.FloorF floorF
            ForallF forallF -> Syntax.ForallF forallF
            IffF iffF -> Syntax.IffF iffF
            ImpliesF impliesF -> Syntax.ImpliesF impliesF
            InF inF -> Syntax.InF inF
            MuF muF -> Syntax.MuF muF
            NextF nextF -> Syntax.NextF nextF
            NotF notF -> Syntax.NotF notF
            NuF nuF -> Syntax.NuF nuF
            OrF orF -> Syntax.OrF orF
            RewritesF rewritesF -> Syntax.RewritesF rewritesF
            StringLiteralF stringLiteralF ->
                Syntax.StringLiteralF stringLiteralF
            CharLiteralF charLiteralF -> Syntax.CharLiteralF charLiteralF
            TopF topF -> Syntax.TopF topF
            VariableF variableF -> Syntax.VariableF variableF
            InhabitantF inhabitantF -> Syntax.InhabitantF inhabitantF
            EvaluatedF evaluatedF ->
                Cofree.tailF
                $ externalizePatternWorker
                $ getEvaluated evaluatedF
            BuiltinF _ -> error "Unexpected internal builtin"

{- | Convert a 'TermLike' to its internal representation.

@internalize@ modifies the term recursively from the bottom up, so any internal
representations are fully normalized.

 -}
internalize
    :: (Ord variable, SortedVariable variable)
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
