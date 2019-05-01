module Test.Kore.Step.MockSimplifiers where

import qualified Data.Map as Map

import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
                 ( wrapPredicate )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (Conditional) )
import qualified Kore.Step.Pattern as Pattern
                 ( Conditional (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..),
                 SimplificationProof (SimplificationProof),
                 termLikeSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )

substitutionSimplifier
    :: SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
substitutionSimplifier tools =
    Predicate.create
        tools
        (termLikeSimplifier
            (\_ p ->
                return
                    ( OrPattern.fromPatterns
                        [ Conditional
                            { term = mkTop_
                            , predicate = Predicate.wrapPredicate p
                            , substitution = mempty
                            }
                        ]
                    , SimplificationProof
                    )
            )
        )
        Map.empty
