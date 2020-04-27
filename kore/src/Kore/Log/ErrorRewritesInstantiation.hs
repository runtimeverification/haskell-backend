{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation (..)
    , errorRewritesInstantiation
    , checkSubstitutionCoverage
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Axiom
    ( Axiom (..)
    , mapAxiomVariables
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    , Variable
    , toVariable
    )
import Kore.Step.RulePattern
    ( RHS (..)
    , RewriteRule (..)
    , RulePattern (..)
    , rewriteRuleToTerm
    )
import Kore.Step.Step
    ( UnifiedRule
    , wouldNarrowWith
    )
import Kore.Unification.Error
import Kore.Unparser
    ( unparse
    )
import Kore.Variables.Target
    ( Target
    , unTarget
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , foldMapVariable
    , mapUnifiedVariable
    )
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data ErrorRewritesInstantiation =
    ErrorRewritesInstantiation
        { problem :: !(Either UnificationError SubstitutionCoverageError)
        , configuration :: !(Pattern Variable)
        }
    deriving (GHC.Generic)

data SubstitutionCoverageError =
    SubstitutionCoverageError
        { solution :: !(UnifiedRule Variable (RewriteRule Variable))
        , missingVariables :: !(Set (UnifiedVariable Variable))
        }

instance SOP.Generic ErrorRewritesInstantiation

instance SOP.HasDatatypeInfo ErrorRewritesInstantiation

instance Entry ErrorRewritesInstantiation where
    entrySeverity _ = Error
    helpDoc _ = "log rewrite instantiation errors"

instance Pretty ErrorRewritesInstantiation where
    pretty
        ErrorRewritesInstantiation
            { problem = Left unificationError, configuration }
      =
        Pretty.vsep
            [ "While rewriting the configuration:"
            , Pretty.indent 4 (unparse configuration)
            , Pretty.indent 2 "unification error:"
            , Pretty.indent 4 (Pretty.pretty unificationError)
            , Pretty.indent 2
                "The unification error above prevented instantiation of \
                \a semantic rule, so execution cannot continue."
            ]
    pretty
        ErrorRewritesInstantiation
            { problem =
                Right SubstitutionCoverageError { solution, missingVariables }
            , configuration
            }
      =
        Pretty.vsep
            [ "While rewriting the configuration:"
            , Pretty.indent 4 (unparse configuration)
            , "Unable to instantiate semantic rule at "
                <> Pretty.pretty location
            , "Unification did not find a solution for the variables:"
            , (Pretty.indent 4 . Pretty.sep)
                (unparse <$> Set.toAscList missingVariables)
            , "The unification solution was:"
            , unparse $ fmap rewriteRuleToTerm solution
            ]
      where
        location = sourceLocation . attributes . getRewriteRule . term $ solution

errorRewritesInstantiation
    :: HasCallStack
    => MonadLog log
    => InternalVariable variable
    => Pattern variable
    -> UnificationError
    -> log a
errorRewritesInstantiation configuration' unificationError = do
    logEntry
        ErrorRewritesInstantiation
        { problem = Left unificationError, configuration }
    error "Aborting execution"
  where
    mapVariables = Pattern.mapVariables (fmap toVariable) (fmap toVariable)
    configuration = mapVariables configuration'

{- | Check that the final substitution covers the applied rule appropriately.

For normal execution, the final substitution should cover all the free
variables on the left-hand side of the applied rule; otherwise, we would
wrongly introduce existentially-quantified variables into the final
configuration. Failure of the coverage check indicates a problem with
unification, so in that case @checkSubstitutionCoverage@ throws
an error message with the axiom and the initial and final configurations.

For symbolic execution, we expect to replace symbolic variables with
more specific patterns (narrowing), so we just quantify the variables
we added to the result.

@checkSubstitutionCoverage@ calls @quantifyVariables@ to remove
the axiom variables from the substitution and unwrap all the 'Target's.
-}
checkSubstitutionCoverage
    :: forall variable monadLog
    .  InternalVariable variable
    => MonadLog monadLog
    => Pattern (Target variable)
    -- ^ Initial configuration
    -> UnifiedRule (Target variable) (RewriteRule (Target variable))
    -- ^ Unified rule
    -> monadLog ()
checkSubstitutionCoverage initial unified
  | isCoveringSubstitution || isSymbolic = return ()
  | otherwise = do
    -- The substitution does not cover all the variables on the left-hand side
    -- of the rule *and* we did not generate a substitution for a symbolic
    -- initial configuration. This is a fatal error because it indicates
    -- something has gone horribly wrong.
    logEntry
        ErrorRewritesInstantiation
        { problem = Right substitutionCoverageError, configuration }
    error "Error! Please report this."
  where
    substitutionCoverageError = SubstitutionCoverageError
        { solution = Conditional
            { term =
                RewriteRule . mapUnTargetRulePattern . getRewriteRule
                $ Pattern.term unified
            , predicate = fmap mapUnTargetTermLike $ Pattern.predicate unified
            , substitution =
                mapUnTargetSubstitution $ Pattern.substitution unified
            }
        , missingVariables =
            Set.map
                ( mapUnifiedVariable
                    (fmap unTargetVariable)
                    (fmap unTargetVariable)
                )
                substitutionVariables
        }
    configuration = Conditional
        { term = mapUnTargetTermLike $ Pattern.term initial
        , predicate = fmap mapUnTargetTermLike $ Pattern.predicate initial
        , substitution = mapUnTargetSubstitution $ Pattern.substitution initial
        }
    mapUnTargetTermLike
        :: TermLike.TermLike (Target variable)
        -> TermLike.TermLike Variable
    mapUnTargetTermLike =
        TermLike.mapVariables (fmap unTargetVariable) (fmap unTargetVariable)
    mapUnTargetSubstitution
        :: Substitution (Target variable)
        -> Substitution Variable
    mapUnTargetSubstitution =
        Substitution.modify
            (fmap
                (Substitution.mapAssignmentVariables
                    (fmap unTargetVariable)
                    (fmap unTargetVariable)
                )
            )
    mapUnTargetRulePattern
        :: RulePattern (Target variable)
        -> RulePattern Variable
    mapUnTargetRulePattern
        RulePattern { left, antiLeft, requires, rhs, attributes}
      =
        RulePattern
            { left = mapUnTargetTermLike left
            , antiLeft = fmap mapUnTargetTermLike antiLeft
            , requires = fmap mapUnTargetTermLike requires
            , rhs = mapUnTargetRHS rhs
            , attributes =
                mapAxiomVariables
                    (fmap unTargetVariable)
                    (fmap unTargetVariable)
                    attributes
            }
    mapUnTargetRHS :: RHS (Target variable) -> RHS Variable
    mapUnTargetRHS RHS { existentials, right, ensures} =
        RHS
            { existentials = (fmap . fmap) unTargetVariable existentials
            , right = mapUnTargetTermLike right
            , ensures = fmap mapUnTargetTermLike ensures
            }
    unTargetVariable :: Target variable -> Variable
    unTargetVariable = toVariable . unTarget

    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)
    uncovered = wouldNarrowWith unified
    isCoveringSubstitution = Set.null uncovered
    isSymbolic =
        Foldable.any (foldMapVariable Target.isNonTarget)
            substitutionVariables
