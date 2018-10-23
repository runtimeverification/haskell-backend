module Test.Kore.Step.MockSimplifiers where

import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
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
                 PureMLPatternSimplifier (PureMLPatternSimplifier),
                 SimplificationProof (SimplificationProof), Simplifier )
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
        (PureMLPatternSimplifier
            (\_ p ->
                return
                    ( OrOfExpandedPattern.make
                        [ Predicated
                            { term = mkTop
                            , predicate = Predicate.wrapPredicate p
                            , substitution = []
                            }
                        ]
                    , SimplificationProof
                    )
            )
        )
