{-|
Module      : Kore.Step.Pattern
Description : Abstract representation of Kore patterns in the evaluator
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Step.Pattern
    ( StepPattern
    , CommonStepPattern
    , ConcreteStepPattern
    , module Kore.AST.MetaOrObject
    , module Kore.AST.Pure
    , mapVariables
    , traverseVariables
    , asConcreteStepPattern
    , fromConcreteStepPattern
    , toKorePattern
    , fromKorePattern
    , toKoreSentence
    , toKoreSentenceAlias
    , toKoreSentenceAxiom
    , toKoreModule
    , substitute
    , externalizeFreshVariables
    ) where

import           Control.Comonad
import qualified Control.Lens as Lens
import           Control.Monad.Reader
                 ( Reader )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import           Kore.Annotation.Valid
                 ( Valid (..) )
import qualified Kore.Annotation.Valid as Valid
import           Kore.AST.Common
                 ( Exists (..), Forall (..), Pattern (..),
                 SortedVariable (..) )
import qualified Kore.AST.Common as Base
import           Kore.AST.Kore
                 ( KorePattern, UnifiedPattern (..), UnifiedSortVariable,
                 asUnifiedPattern )
import           Kore.AST.MetaOrObject
import           Kore.AST.Pure
                 ( CofreeF (..), Concrete, Pattern, PurePattern, Variable )
import           Kore.AST.Sentence
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.Sort
import qualified Kore.Substitute as Substitute
import           Kore.Variables.Fresh

type StepPattern level variable =
    PurePattern level Domain.Builtin variable (Valid (variable level) level)

type CommonStepPattern level = StepPattern level Variable

type ConcreteStepPattern level = StepPattern level Concrete

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord (variable2 level)
    => (variable1 level -> variable2 level)
    -> StepPattern level variable1
    -> StepPattern level variable2
mapVariables mapping =
    Recursive.unfold (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (valid :< pat) =
        Valid.mapVariables mapping valid :< Base.mapVariables mapping pat

{- | Use the provided traversal to replace all variables in a 'StepPattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m level variable1 variable2.
        (Monad m, Ord (variable2 level))
    => (variable1 level -> m (variable2 level))
    -> StepPattern level variable1
    -> m (StepPattern level variable2)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker (valid :< pat) =
        Recursive.embed <$> projected
      where
        projected =
            (:<)
                <$> Valid.traverseVariables traversing valid
                <*> (Base.traverseVariables traversing =<< sequence pat)

{- | Construct a 'ConcreteStepPattern' from a 'StepPattern'.

A concrete pattern contains no variables, so @asConcreteStepPattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcreteStepPattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcreteStepPattern
    :: StepPattern level variable
    -> Maybe (StepPattern level Concrete)
asConcreteStepPattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'StepPattern' from a 'ConcreteStepPattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcreteStepPattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcreteStepPattern
    :: Ord (variable level)
    => StepPattern level Concrete
    -> StepPattern level variable
fromConcreteStepPattern = mapVariables (\case {})

{- | Convert a leveled 'StepPattern' to a unified 'KorePattern'.
 -}
toKorePattern
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        )
    => StepPattern level variable
    -> KorePattern Domain.Builtin variable (Unified annotation)
toKorePattern =
    Recursive.unfold toKorePatternWorker
  where
    toKorePatternWorker (Recursive.project -> ann :< pat) =
        asUnified (Valid.mapVariables asUnified ann) :< asUnifiedPattern pat

{- | Extract a 'StepPattern' from a 'KorePattern'.

@patternKoreToStep@ does not lift the term, but rather fails with 'koreFail'
if any part of the pattern is on a different level.  For lifting functions see
"Kore.MetaML.Lift".

 -}
fromKorePattern
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        )
    => level
    -> KorePattern Domain.Builtin variable (Unified annotation)
    -> Either (Error a) (StepPattern level variable)
fromKorePattern level =
    Recursive.fold (extractStepPattern $ isMetaOrObject $ toProxy level)

extractStepPattern
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        , result ~ StepPattern level variable
        )
    => IsMetaOrObject level
    -> Base
        (KorePattern Domain.Builtin variable (Unified annotation))
        (Either (Error e) result)
    -> Either (Error e) result
extractStepPattern IsMeta = \(ann :< pat) ->
    case pat of
        UnifiedMetaPattern mpat ->
            case ann of
                UnifiedMeta mann ->
                  do
                    mpat' <- sequence mpat
                    mann' <- Valid.traverseVariables extractMetaVariable mann
                    (return . Recursive.embed) (mann' :< mpat')
                  where
                    extractMetaVariable = extractVariable IsMeta
                UnifiedObject _ ->
                    koreFail "Unexpected object-level annotation"
        UnifiedObjectPattern _ ->
            koreFail "Unexpected object-level pattern"
extractStepPattern IsObject = \(ann :< pat) ->
    case pat of
        UnifiedObjectPattern opat ->
            case ann of
                UnifiedObject oann ->
                  do
                    opat' <- sequence opat
                    oann' <- Valid.traverseVariables extractObjectVariable oann
                    (return . Recursive.embed) (oann' :< opat')
                  where
                    extractObjectVariable = extractVariable IsObject
                UnifiedMeta _ ->
                    koreFail "Unexpected meta-level annotation"
        UnifiedMetaPattern _ ->
            koreFail "Unexpected meta-level pattern"

extractVariable
    :: IsMetaOrObject level
    -> Unified variable
    -> Either (Error e) (variable level)
extractVariable =
    \case
        IsMeta ->
            \case
                UnifiedObject _ -> koreFail "Expected meta-variable"
                UnifiedMeta mvar -> return mvar
        IsObject ->
            \case
                UnifiedObject ovar -> return ovar
                UnifiedMeta _ -> koreFail "Expected object-variable"

{- | Convert a 'Sentence' over 'StepPattern' to a 'KorePattern' sentence.
 -}
toKoreSentence
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        )
    => Sentence level (SortVariable level) (StepPattern level variable)
    -> UnifiedSentence UnifiedSortVariable
        (KorePattern Domain.Builtin variable (Unified annotation))
toKoreSentence (SentenceAliasSentence sa) =
    asSentence $ toKoreSentenceAlias sa
toKoreSentence (SentenceSymbolSentence (SentenceSymbol a b c d)) =
    constructUnifiedSentence SentenceSymbolSentence $ SentenceSymbol a b c d
toKoreSentence (SentenceImportSentence (SentenceImport a b)) =
    constructUnifiedSentence SentenceImportSentence $ SentenceImport a b
toKoreSentence (SentenceAxiomSentence msx) =
    asKoreAxiomSentence $ toKoreSentenceAxiom msx
toKoreSentence (SentenceClaimSentence msx) =
    asKoreClaimSentence $ toKoreSentenceAxiom msx
toKoreSentence (SentenceSortSentence mss) =
  constructUnifiedSentence SentenceSortSentence mss
    { sentenceSortName = sentenceSortName mss
    , sentenceSortParameters = sentenceSortParameters mss
    }
toKoreSentence (SentenceHookSentence hooked) =
    case hooked of
        SentenceHookedSort mss ->
            constructUnifiedSentence
                (SentenceHookSentence . SentenceHookedSort)
                mss
                    { sentenceSortName = sentenceSortName mss
                    , sentenceSortParameters = sentenceSortParameters mss
                    }
        SentenceHookedSymbol (SentenceSymbol a b c d) ->
            constructUnifiedSentence
                (SentenceHookSentence . SentenceHookedSymbol)
                (SentenceSymbol a b c d)

{- | Convert a 'SentenceAlias' over 'StepPattern' to a 'KorePattern' sentence.
 -}
toKoreSentenceAlias
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        )
    => SentenceAlias level (StepPattern level variable)
    -> SentenceAlias level
        (KorePattern Domain.Builtin variable (Unified annotation))
toKoreSentenceAlias = (<$>) toKorePattern

{- | Convert a 'SentenceAxiom' over 'StepPattern' to a 'KorePattern' sentence.
 -}
toKoreSentenceAxiom
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        )
    => SentenceAxiom (SortVariable level) (StepPattern level variable)
    -> SentenceAxiom UnifiedSortVariable
        (KorePattern Domain.Builtin variable (Unified annotation))
toKoreSentenceAxiom = unifyAxiomParameters . (<$>) toKorePattern
  where
    unifyAxiomParameters axiom@SentenceAxiom { sentenceAxiomParameters } =
        axiom
            { sentenceAxiomParameters =
                asUnified <$> sentenceAxiomParameters
            }

{- | Convert a 'Module' over 'StepPattern' sentences to 'KorePattern' sentences.
 -}
toKoreModule
    ::  ( MetaOrObject level
        , OrdMetaOrObject variable
        , annotation ~ Valid (Unified variable)
        , stepPattern ~ StepPattern level variable
        , korePattern ~ KorePattern Domain.Builtin variable (Unified annotation)
        )
    => Module (Sentence level (SortVariable level) stepPattern)
    -> Module (UnifiedSentence UnifiedSortVariable korePattern)
toKoreModule mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map toKoreSentence (moduleSentences mm)
    , moduleAttributes =  moduleAttributes mm
    }

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
substitute
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        )
    => Map (variable level) (StepPattern level variable)
    -> StepPattern level variable
    -> StepPattern level variable
substitute = Substitute.substitute (Lens.lens getFreeVariables setFreeVariables)
  where
    getFreeVariables Valid { freeVariables } = freeVariables
    setFreeVariables valid freeVariables = valid { freeVariables }

{- | Reset the 'variableCounter' of all 'Variables'.

@externalizeFreshVariables@ resets the 'variableCounter' of all variables, while
ensuring that no 'Variable' in the result is accidentally captured.

 -}
externalizeFreshVariables
    :: forall level. MetaOrObject level
    => StepPattern level Variable
    -> StepPattern level Variable
externalizeFreshVariables stepPattern =
    Reader.runReader
        (Recursive.fold externalizeFreshVariablesWorker stepPattern)
        renamedFreeVariables
  where
    -- | 'originalFreeVariables' are present in the original pattern; they do
    -- not have a generated counter. 'generatedFreeVariables' have a generated
    -- counter, usually because they were introduced by applying some axiom.
    (originalFreeVariables, generatedFreeVariables) =
        Set.partition Base.isOriginalVariable freeVariables
      where
        Valid { freeVariables } = extract stepPattern

    -- | The map of generated free variables, renamed to be unique from the
    -- original free variables.
    (renamedFreeVariables, _) =
        Foldable.foldl' rename initial generatedFreeVariables
      where
        initial = (Map.empty, originalFreeVariables)
        rename (renaming, avoiding) variable =
            let
                variable' = safeVariable avoiding variable
                renaming' = Map.insert variable variable' renaming
                avoiding' = Set.insert variable' avoiding
            in
                (renaming', avoiding')

    {- | Look up a variable renaming.

    The original (not generated) variables of the pattern are never renamed, so
    these variables are not present in the Map of renamed variables.

     -}
    lookupVariable variable =
        Reader.asks (Map.lookup variable) >>= \case
            Nothing -> return variable
            Just variable' -> return variable'

    {- | Externalize a variable safely.

    The variable's counter is incremented until its externalized form is unique
    among the set of avoided variables. The externalized form is returned.

     -}
    safeVariable avoiding variable =
        head  -- 'head' is safe because 'iterate' creates an infinite list
        $ dropWhile wouldCapture
        $ Base.externalizeFreshVariable
        <$> iterate nextVariable variable
      where
        wouldCapture var = Set.member var avoiding

    underBinder freeVariables' variable child = do
        let variable' = safeVariable freeVariables' variable
        child' <- Reader.local (Map.insert variable variable') child
        return (variable', child')

    externalizeFreshVariablesWorker
        ::  Base
                (CommonStepPattern level)
                (Reader
                    (Map (Variable level) (Variable level))
                    (CommonStepPattern level)
                )
        ->  (Reader
                (Map (Variable level) (Variable level))
                (CommonStepPattern level)
            )
    externalizeFreshVariablesWorker (valid :< patt) = do
        valid' <- Valid.traverseVariables lookupVariable valid
        let Valid { freeVariables = freeVariables' } = valid'
        patt' <-
            case patt of
                ExistsPattern exists -> do
                    let Exists { existsVariable, existsChild } = exists
                    (existsVariable', existsChild') <-
                        underBinder
                            freeVariables'
                            existsVariable
                            existsChild
                    let exists' =
                            exists
                                { existsVariable = existsVariable'
                                , existsChild = existsChild'
                                }
                    return (ExistsPattern exists')
                ForallPattern forall -> do
                    let Forall { forallVariable, forallChild } = forall
                    (forallVariable', forallChild') <-
                        underBinder
                            freeVariables'
                            forallVariable
                            forallChild
                    let forall' =
                            forall
                                { forallVariable = forallVariable'
                                , forallChild = forallChild'
                                }
                    return (ForallPattern forall')
                _ ->
                    Base.traverseVariables lookupVariable patt >>= sequence
        (return . Recursive.embed) (valid' :< patt')
