module Test.Kore.Step.MockSimplifiers where

import qualified Data.Map as Map

import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
                 ( wrapPredicate )
import           Kore.Step.Pattern
                 ( Conditional (Conditional) )
import qualified Kore.Step.Pattern as Pattern
                 ( Conditional (..) )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..),
                 SimplificationProof (SimplificationProof),
                 stepPatternSimplifier )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
                 ( create )

substitutionSimplifier
    :: SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
substitutionSimplifier tools =
    PredicateSubstitution.create
        tools
        (stepPatternSimplifier
            (\_ p ->
                return
                    ( MultiOr.make
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
