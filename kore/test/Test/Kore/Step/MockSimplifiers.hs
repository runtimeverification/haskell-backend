module Test.Kore.Step.MockSimplifiers where

import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..) )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )

substitutionSimplifier :: PredicateSimplifier
substitutionSimplifier = Predicate.create
