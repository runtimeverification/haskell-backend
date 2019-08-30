module Test.Kore.Step.MockSimplifiers where

import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( wrapPredicate )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify (..), PredicateSimplifier (..),
                 termLikeSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )

substitutionSimplifier :: PredicateSimplifier
substitutionSimplifier =
    PredicateSimplifier $ \predicate ->
        localSimplifierTermLike (const simplifierWrapPredicate)
        $ predicateSimplifier predicate
  where
    -- TODO (thomas.tuegel): Remove simplifierWrapPredicate.
    simplifierWrapPredicate =
        termLikeSimplifier $ \_ patt ->
            (return . OrPattern.fromPattern)
                (Pattern.topOf (termLikeSort patt))
                    { Pattern.predicate = wrapPredicate patt }
    PredicateSimplifier predicateSimplifier = Predicate.create
