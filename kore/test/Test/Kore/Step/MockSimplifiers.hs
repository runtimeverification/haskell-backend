module Test.Kore.Step.MockSimplifiers where

import qualified Data.Map as Map

import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Pattern as Pattern
                 ( Conditional (..) )
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Predicate
                 ( wrapPredicate )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..), termLikeSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )

substitutionSimplifier :: PredicateSimplifier
substitutionSimplifier =
    Predicate.create
        (termLikeSimplifier $ \_ p ->
            return $ OrPattern.fromPattern
                Conditional
                    { term = mkTop_
                    , predicate = Predicate.wrapPredicate p
                    , substitution = mempty
                    }
        )
        Map.empty
