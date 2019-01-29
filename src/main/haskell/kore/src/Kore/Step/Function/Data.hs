{-|
Module      : Kore.Step.Function.Data
Description : Data structures used for function evaluation.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Data
    ( BuiltinAndAxiomSimplifier (..)
    , BuiltinAndAxiomSimplifierMap
    , AttemptedAxiom (..)
    , BuiltinAndAxiomsFunctionEvaluator
    , CommonAttemptedAxiom
    , FunctionEvaluators (..)
    , applicationAxiomSimplifier
    , notApplicableAxiomEvaluator
    , purePatternAxiomEvaluator
    ) where

import qualified Data.Map.Strict as Map
import           Data.These
                 ( These )

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.AxiomPatterns
       ( EqualityRule )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern, makeFromSinglePurePattern )
import Kore.Step.Pattern
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof (..), Simplifier,
       StepPatternSimplifier )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

{-| 'BuiltinAndAxiomSimplifier' simplifies 'Application' patterns using either an axiom
or builtin code.

Arguments:

* 'MetadataTools' are tools for finding additional information about
patterns such as their sorts, whether they are constructors or hooked.

* 'StepPatternSimplifier' is a Function for simplifying patterns, used for
the post-processing of the function application results.

* 'Application' is the pattern to be evaluated.

Return value:

It returns the result of appling the function, together with a proof certifying
that the function was applied correctly (which is only a placeholder right now).
-}
newtype BuiltinAndAxiomSimplifier level =
    BuiltinAndAxiomSimplifier
        (forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , SortedVariable variable
            , Show (variable level)
            , Show (variable Object)
            , Unparse (variable level)
            , ShowMetaOrObject variable
            )
        => MetadataTools level StepperAttributes
        -> PredicateSubstitutionSimplifier level Simplifier
        -> StepPatternSimplifier level variable
        -> StepPattern level variable
        -> Simplifier
            ( AttemptedAxiom level variable
            , SimplificationProof level
            )
        )

{-| Data structure for holding evaluators for the same symbol
-}
data FunctionEvaluators level
    = FunctionEvaluators
        { definitionRules :: [EqualityRule level]
        -- ^ Evaluators used when evaluating functions according to their
        -- definition.
        , simplificationEvaluators :: [BuiltinAndAxiomSimplifier level]
        -- ^ Evaluators used when simplifying functions.
        }

{-|Datastructure to combine both a builtin evaluator and axiom-based
function evaluators for the same symbol.

The backend implementation allows symbols to both be hooked to a builtin
implementation and to be defined through axioms;  however, we don't want to
use both methods to evaluate the function at the same time.  That is because
(1) we expect to get the same results; (2) when one of them fails while the
other succeeds, using both results would introduce a split in the search space.
-}
type BuiltinAndAxiomsFunctionEvaluator level =
    These
        (BuiltinAndAxiomSimplifier level)
        (FunctionEvaluators level)

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap level =
    Map.Map (Id level) (BuiltinAndAxiomsFunctionEvaluator level)

{-| 'AttemptedAxiom' hods the result of axiom-based simplification, with
a case for axioms that can't be applied.
-}
data AttemptedAxiom level variable
    = NotApplicable
    | Applied !(OrOfExpandedPattern level variable)
  deriving (Show, Eq)

{-| 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom level = AttemptedAxiom level Variable

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableAxiomEvaluator
    :: Simplifier
        (AttemptedAxiom level1 variable, SimplificationProof level2)
notApplicableAxiomEvaluator = pure (NotApplicable, SimplificationProof)

-- |Yields a pure 'Simplifier' which produces a given 'StepPattern'
purePatternAxiomEvaluator
    :: (MetaOrObject level, Ord (variable level))
    => StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
purePatternAxiomEvaluator p =
    pure
        ( Applied (makeFromSinglePurePattern p)
        , SimplificationProof
        )

{-| Creates an 'BuiltinAndAxiomSimplifier' from a similar function that takes an
'Application'.
-}
applicationAxiomSimplifier
    :: forall level
    .   ( forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , SortedVariable variable
            , Show (variable level)
            , Show (variable Object)
            , Unparse (variable level)
            , ShowMetaOrObject variable
            )
        => MetadataTools level StepperAttributes
        -> PredicateSubstitutionSimplifier level Simplifier
        -> StepPatternSimplifier level variable
        -> CofreeF
            (Application level)
            (Valid (variable level) level)
            (StepPattern level variable)
        -> Simplifier
            ( AttemptedAxiom level variable
            , SimplificationProof level
            )
        )
    -> BuiltinAndAxiomSimplifier level
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper
        ::  ( forall variable
            .   ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , OrdMetaOrObject variable
                , SortedVariable variable
                , Show (variable level)
                , Show (variable Object)
                , Unparse (variable level)
                , ShowMetaOrObject variable
                )
            => MetadataTools level StepperAttributes
            -> PredicateSubstitutionSimplifier level Simplifier
            -> StepPatternSimplifier level variable
            -> StepPattern level variable
            -> Simplifier
                ( AttemptedAxiom level variable
                , SimplificationProof level
                )
        )
    helper
        tools
        substitutionSimplifier
        simplifier
        patt
      =
        case fromPurePattern patt of
            (valid :< ApplicationPattern p) ->
                applicationSimplifier
                    tools substitutionSimplifier simplifier (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show patt)

