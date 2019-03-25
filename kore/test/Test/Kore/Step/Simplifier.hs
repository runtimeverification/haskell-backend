module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.Pattern
import qualified Kore.Step.Pattern as Pattern
                 ( mapVariables )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( mapVariables )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

mockSimplifier
    ::  ( MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        )
    =>  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> StepPatternSimplifier level
mockSimplifier values =
    StepPatternSimplifier
        ( mockSimplifierHelper
            (\patt -> Predicated
                { term = patt
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            )
            values
        )

mockPredicateSimplifier
    ::  ( MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        )
    =>  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> StepPatternSimplifier level
mockPredicateSimplifier values =
    StepPatternSimplifier
        (mockSimplifierHelper
            (\patt -> Predicated
                { term = mkTop_
                , predicate = wrapPredicate patt
                , substitution = mempty
                }
            )
            values
        )

mockSimplifierHelper
    ::  ( FreshVariable variable0
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable0 level)
        , OrdMetaOrObject variable0
        , Show (variable0 level)
        , ShowMetaOrObject variable0
        , Unparse (variable0 level)
        , SortedVariable variable
        , SortedVariable variable0
        )
    =>  (StepPattern level variable -> ExpandedPattern level variable)
    ->  [   ( StepPattern level variable
            , ([ExpandedPattern level variable], SimplificationProof level)
            )
        ]
    -> PredicateSubstitutionSimplifier level
    -> StepPattern level variable0
    -> Simplifier
        (OrOfExpandedPattern level variable0, SimplificationProof level)
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
    ::  ( Ord (variable0 level)
        , SortedVariable variable
        , SortedVariable variable0
        )
    => StepPattern level variable
    -> StepPattern level variable0
convertPatternVariables = Pattern.mapVariables (fromVariable . toVariable)

convertExpandedVariables
    ::  ( Ord (variable0 level)
        , SortedVariable variable
        , SortedVariable variable0
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable0
convertExpandedVariables =
    ExpandedPattern.mapVariables (fromVariable . toVariable)
