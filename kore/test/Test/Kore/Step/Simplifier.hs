module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( wrapPredicate
    )
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Variable
    ( SortedVariable (..)
    )

mockSimplifier
    :: SimplifierVariable variable
    => [(TermLike variable, [Pattern variable])]
    -> TermLikeSimplifier
mockSimplifier values =
    termLikeSimplifier
        $ const $ mockSimplifierHelper Pattern.fromTermLike values

mockPredicateSimplifier
    :: SimplifierVariable variable
    => [(TermLike variable, [Pattern variable])]
    -> TermLikeSimplifier
mockPredicateSimplifier values =
    termLikeSimplifier $ const $
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
    ::  ( SimplifierVariable variable0
        , SimplifierVariable variable
        , MonadSimplify m
        )
    => (TermLike variable -> Pattern variable)
    -> [(TermLike variable, [Pattern variable])]
    -> TermLike variable0
    -> m (OrPattern variable0)
mockSimplifierHelper unevaluatedConverter [] patt =
    return
        ( OrPattern.fromPatterns
            [ convertPatternVariables
                (unevaluatedConverter (convertTermLikeVariables patt))
            ]

        )
mockSimplifierHelper
    unevaluatedConverter
    ((patt, patts) : reminder)
    unevaluatedPatt
  | patt == convertTermLikeVariables unevaluatedPatt
  = return $ OrPattern.fromPatterns $ map convertPatternVariables patts
  | otherwise =
    mockSimplifierHelper
        unevaluatedConverter
        reminder
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
