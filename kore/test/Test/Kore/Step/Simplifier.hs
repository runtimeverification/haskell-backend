module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike as TermLike
import           Kore.Predicate.Predicate
                 ( wrapPredicate )
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
            [ convertPatternVariables
                (unevaluatedConverter (convertTermLikeVariables patt))
            ]

        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, patts) : reminder)
    substitutionSimplifier
    unevaluatedPatt
  | patt == convertTermLikeVariables unevaluatedPatt
  = return $ OrPattern.fromPatterns $ map convertPatternVariables patts
  | otherwise =
    mockSimplifierHelper
        unevaluatedConverter
        reminder
        substitutionSimplifier
        unevaluatedPatt

convertTermLikeVariables
    ::  ( Ord variable0
        , SortedVariable variable
        , SortedVariable variable0
        )
    => TermLike variable
    -> TermLike variable0
convertTermLikeVariables =
    TermLike.mapVariables (fromVariable . toVariable)

convertPatternVariables
    ::  ( Ord variable
        , Ord variable0
        , SortedVariable variable
        , SortedVariable variable0
        )
    => Pattern variable
    -> Pattern variable0
convertPatternVariables =
    Pattern.mapVariables (fromVariable . toVariable)
