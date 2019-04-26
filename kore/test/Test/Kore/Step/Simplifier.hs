module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( Conditional (..), ExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( mapVariables )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier, stepPatternSimplifier )
import           Kore.Step.TermLike
                 ( TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

mockSimplifier
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([ExpandedPattern Object variable], SimplificationProof Object)
            )
        ]
    -> StepPatternSimplifier Object
mockSimplifier values =
    stepPatternSimplifier
        ( mockSimplifierHelper
            (\patt -> Conditional
                { term = patt
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            )
            values
        )

mockPredicateSimplifier
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([ExpandedPattern Object variable], SimplificationProof Object)
            )
        ]
    -> StepPatternSimplifier Object
mockPredicateSimplifier values =
    stepPatternSimplifier
        (mockSimplifierHelper
            (\patt -> Conditional
                { term = mkTop_
                , predicate = wrapPredicate patt
                , substitution = mempty
                }
            )
            values
        )

mockSimplifierHelper
    ::  ( FreshVariable variable0
        , MetaOrObject Object
        , Ord (variable Object)
        , Ord (variable0 Object)
        , OrdMetaOrObject variable0
        , Show (variable0 Object)
        , ShowMetaOrObject variable0
        , Unparse (variable0 Object)
        , SortedVariable variable
        , SortedVariable variable0
        )
    =>  (TermLike variable -> ExpandedPattern Object variable)
    ->  [   ( TermLike variable
            , ([ExpandedPattern Object variable], SimplificationProof Object)
            )
        ]
    -> PredicateSubstitutionSimplifier Object
    -> TermLike variable0
    -> Simplifier
        (OrOfExpandedPattern Object variable0, SimplificationProof Object)
mockSimplifierHelper unevaluatedConverter [] _ patt =
    return
        ( MultiOr.make
            [ convertExpandedVariables
                (unevaluatedConverter (convertPatternVariables patt))
            ]
        , SimplificationProof
        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, (patts, proof)) : reminder)
    substitutionSimplifier
    unevaluatedPatt
  =
    if patt == convertPatternVariables unevaluatedPatt
        then return
            ( MultiOr.make (map convertExpandedVariables patts)
            , proof
            )
        else
            mockSimplifierHelper
                unevaluatedConverter
                reminder
                substitutionSimplifier
                unevaluatedPatt

convertPatternVariables
    ::  ( Ord (variable0 Object)
        , SortedVariable variable
        , SortedVariable variable0
        )
    => TermLike variable
    -> TermLike variable0
convertPatternVariables = TermLike.mapVariables (fromVariable . toVariable)

convertExpandedVariables
    ::  ( Ord (variable0 Object)
        , SortedVariable variable
        , SortedVariable variable0
        )
    => ExpandedPattern Object variable
    -> ExpandedPattern Object variable0
convertExpandedVariables =
    ExpandedPattern.mapVariables (fromVariable . toVariable)
