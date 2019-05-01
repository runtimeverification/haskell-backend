module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Pattern as Pattern
                 ( mapVariables )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier, termLikeSimplifier )
import           Kore.Step.TermLike
                 ( Object, TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.Syntax.Variable
                 ( SortedVariable (..) )
import           Kore.Variables.Fresh
                 ( FreshVariable )

mockSimplifier
    ::  ( Ord variable
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([Pattern variable], SimplificationProof Object)
            )
        ]
    -> TermLikeSimplifier Object
mockSimplifier values =
    termLikeSimplifier
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
    ::  ( Ord variable
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([Pattern variable], SimplificationProof Object)
            )
        ]
    -> TermLikeSimplifier Object
mockPredicateSimplifier values =
    termLikeSimplifier
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
        , Ord variable
        , SortedVariable variable
        , SortedVariable variable0
        )
    =>  (TermLike variable -> Pattern variable)
    ->  [   ( TermLike variable
            , ([Pattern variable], SimplificationProof Object)
            )
        ]
    -> PredicateSimplifier Object
    -> TermLike variable0
    -> Simplifier
        (OrPattern variable0, SimplificationProof Object)
mockSimplifierHelper unevaluatedConverter [] _ patt =
    return
        ( OrPattern.fromPatterns
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
            ( OrPattern.fromPatterns (map convertExpandedVariables patts)
            , proof
            )
        else
            mockSimplifierHelper
                unevaluatedConverter
                reminder
                substitutionSimplifier
                unevaluatedPatt

convertPatternVariables
    ::  ( Ord variable0
        , SortedVariable variable
        , SortedVariable variable0
        )
    => TermLike variable
    -> TermLike variable0
convertPatternVariables = TermLike.mapVariables (fromVariable . toVariable)

convertExpandedVariables
    ::  ( Ord variable0
        , SortedVariable variable
        , SortedVariable variable0
        )
    => Pattern variable
    -> Pattern variable0
convertExpandedVariables =
    Pattern.mapVariables (fromVariable . toVariable)
