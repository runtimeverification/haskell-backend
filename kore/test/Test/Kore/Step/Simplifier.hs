module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockConditionSimplifier
    ) where

import Prelude.Kore

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( wrapPredicate
    )
import Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.Simplify

mockSimplifier
    :: InternalVariable variable
    => [(TermLike variable, [Pattern variable])]
    -> TermLikeSimplifier
mockSimplifier values =
    termLikeSimplifier
        $ const $ mockSimplifierHelper Pattern.fromTermLike values

mockConditionSimplifier
    :: InternalVariable variable
    => [(TermLike variable, [Pattern variable])]
    -> TermLikeSimplifier
mockConditionSimplifier values =
    termLikeSimplifier $ const
    $ mockSimplifierHelper
        (\patt -> Conditional
            { term = mkTop_
            , predicate = wrapPredicate patt
            , substitution = mempty
            }
        )
        values

mockSimplifierHelper
    ::  ( InternalVariable variable0
        , InternalVariable variable
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
    ::  ( VariableName variable
        , VariableName variable0
        , FreshPartialOrd variable0
        , SortedVariable variable0
        )
    => TermLike variable
    -> TermLike variable0
convertTermLikeVariables =
    TermLike.mapVariables
        (fmap $ fromVariable . toVariable)
        (fmap $ fromVariable . toVariable)

convertPatternVariables
    ::  ( VariableName variable
        , VariableName variable0
        , FreshPartialOrd variable0
        , SortedVariable variable0
        )
    => Pattern variable
    -> Pattern variable0
convertPatternVariables =
    Pattern.mapVariables
        (fmap $ fromVariable . toVariable)
        (fmap $ fromVariable . toVariable)
