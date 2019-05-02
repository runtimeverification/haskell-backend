module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.Internal.TermLike as TermLike
import           Kore.Predicate.Predicate
                 ( wrapPredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier,
                 termLikeSimplifier )
import           Kore.Syntax.Variable
                 ( SortedVariable (..) )
import           Kore.Variables.Fresh
                 ( FreshVariable )

mockSimplifier
    :: (Ord variable, SortedVariable variable)
    => [(TermLike variable, [Pattern variable])]
    -> TermLikeSimplifier
mockSimplifier values =
    termLikeSimplifier $ mockSimplifierHelper Pattern.fromTermLike values

mockPredicateSimplifier
    ::  ( Ord variable
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([Pattern variable])
            )
        ]
    -> TermLikeSimplifier
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
    => (TermLike variable -> Pattern variable)
    -> [(TermLike variable, [Pattern variable])]
    -> PredicateSimplifier
    -> TermLike variable0
    -> Simplifier (OrPattern variable0)
mockSimplifierHelper unevaluatedConverter [] _ patt =
    return
        ( OrPattern.fromPatterns
            [ convertExpandedVariables
                (unevaluatedConverter (convertPatternVariables patt))
            ]

        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, patts) : reminder)
    substitutionSimplifier
    unevaluatedPatt
  | patt == convertPatternVariables unevaluatedPatt
  = return $ OrPattern.fromPatterns $ map convertExpandedVariables patts
  | otherwise =
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
