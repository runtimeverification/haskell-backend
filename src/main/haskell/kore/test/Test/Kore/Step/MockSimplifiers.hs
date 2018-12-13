module Test.Kore.Step.MockSimplifiers where

import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
                 ( wrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (Predicated) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier (StepPatternSimplifier) )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

substitutionSimplifier
    :: MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
substitutionSimplifier tools =
    PredicateSubstitution.create
        tools
        (StepPatternSimplifier
            (\_ p ->
                return
                    ( OrOfExpandedPattern.make
                        [ Predicated
                            { term = mkTop_
                            , predicate = Predicate.wrapPredicate p
                            , substitution = mempty
                            }
                        ]
                    , SimplificationProof
                    )
            )
        )
