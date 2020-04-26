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
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Variable
    ( InternalVariable
    , Variable
    , toVariable
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern
    ( RewriteRule (..)
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
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , foldMapVariable
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
        { solution :: !(UnifiedRule RewriteRule RewritingVariable)
        , missingVariables :: !(Set (UnifiedVariable RewritingVariable))
        }

instance SOP.Generic ErrorRewritesInstantiation

instance SOP.HasDatatypeInfo ErrorRewritesInstantiation

instance Entry ErrorRewritesInstantiation where
    entrySeverity _ = Error

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
    :: forall monadLog
    .  MonadLog monadLog
    => Pattern RewritingVariable
    -- ^ Initial configuration
    -> UnifiedRule RewriteRule RewritingVariable
    -- ^ Unified rule
    -> monadLog ()
checkSubstitutionCoverage initial solution
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
    substitutionCoverageError =
        SubstitutionCoverageError { solution, missingVariables }
    configuration = unwrapConfiguration initial

    Conditional { substitution } = solution
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)
    missingVariables = wouldNarrowWith solution
    isCoveringSubstitution = Set.null missingVariables
    isSymbolic =
        Foldable.any (foldMapVariable isConfigVariable)
            substitutionVariables
