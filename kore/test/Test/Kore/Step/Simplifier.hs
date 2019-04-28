module Test.Kore.Step.Simplifier
    ( mockSimplifier
    , mockPredicateSimplifier
    ) where

import           Kore.AST.Common
                 ( SortedVariable (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate, wrapPredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Pattern as Pattern
                 ( mapVariables )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier, termLikeSimplifier )
import           Kore.Step.TermLike
                 ( Object, TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

mockSimplifier
    ::  ( Ord (variable Object)
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([Pattern Object variable], SimplificationProof Object)
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
    ::  ( Ord (variable Object)
        , SortedVariable variable
        )
    =>  [   ( TermLike variable
            , ([Pattern Object variable], SimplificationProof Object)
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
        , Ord (variable Object)
        , Ord (variable0 Object)
        , Show (variable0 Object)
        , Unparse (variable0 Object)
        , SortedVariable variable
        , SortedVariable variable0
        )
    =>  (TermLike variable -> Pattern Object variable)
    ->  [   ( TermLike variable
            , ([Pattern Object variable], SimplificationProof Object)
            )
        ]
    -> PredicateSimplifier Object
    -> TermLike variable0
    -> Simplifier
        (OrPattern Object variable0, SimplificationProof Object)
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
    => Pattern Object variable
    -> Pattern Object variable0
convertExpandedVariables =
    Pattern.mapVariables (fromVariable . toVariable)
