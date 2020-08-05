{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation (..)
    , checkSubstitutionCoverage
    ) where

import Prelude.Kore

import Control.Exception
    ( Exception (..)
    , throw
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import GHC.Exception
    ( prettyCallStackLines
    )
import qualified GHC.Generics as GHC
import GHC.Stack
    ( CallStack
    , callStack
    )

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
    ( isConstructorLike
    )
import Kore.Internal.Variable
    ( SomeVariableName
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
import Kore.Unparser
    ( unparse
    )
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data ErrorRewritesInstantiation =
    ErrorRewritesInstantiation
        { problem :: !SubstitutionCoverageError
        , configuration :: !(Pattern RewritingVariableName)
        , errorCallStack :: !CallStack
        }
    deriving (Show, GHC.Generic)

data SubstitutionCoverageError =
    SubstitutionCoverageError
        { solution :: !(UnifiedRule RewriteRule RewritingVariableName)
        , missingVariables :: !(Set (SomeVariableName RewritingVariableName))
        }
    deriving (Show)

instance SOP.Generic ErrorRewritesInstantiation

instance SOP.HasDatatypeInfo ErrorRewritesInstantiation

instance Exception ErrorRewritesInstantiation where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= \entry -> fromEntry entry

instance Entry ErrorRewritesInstantiation where
    entrySeverity _ = Error
    helpDoc _ = "log rewrite instantiation errors"

instance Pretty ErrorRewritesInstantiation where
    pretty
        ErrorRewritesInstantiation
            { problem =
                SubstitutionCoverageError { solution, missingVariables }
            , configuration
            , errorCallStack
            }
      =
        Pretty.vsep $
            [ "While rewriting the configuration:"
            , Pretty.indent 4 (unparse configuration)
            , "Unable to instantiate semantic rule at "
                <> Pretty.pretty location
            , "Unification did not find a solution for the variables:"
            , (Pretty.indent 4 . Pretty.sep)
                (unparse <$> Set.toAscList missingVariables)
            , "The unification solution was:"
            , unparse $ fmap rewriteRuleToTerm solution
            , "Error! Please report this."
            ]
            <> fmap Pretty.pretty (prettyCallStackLines errorCallStack)
      where
        location = sourceLocation . attributes . getRewriteRule . term $ solution

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
    => HasCallStack
    => Pattern RewritingVariableName
    -- ^ Initial configuration
    -> UnifiedRule RewriteRule RewritingVariableName
    -- ^ Unified rule
    -> monadLog ()
checkSubstitutionCoverage configuration solution
  | isCoveringSubstitution || isSymbolic = return ()
  | otherwise =
    -- The substitution does not cover all the variables on the left-hand side
    -- of the rule *and* we did not generate a substitution for a symbolic
    -- initial configuration. This is a fatal error because it indicates
    -- something has gone horribly wrong.
    throw
        ErrorRewritesInstantiation
        { problem = substitutionCoverageError
        , configuration
        , errorCallStack = callStack
        }
  where
    substitutionCoverageError =
        SubstitutionCoverageError { solution, missingVariables }

    missingVariables = wouldNarrowWith solution
    isCoveringSubstitution = Set.null missingVariables
    isSymbolic = (not . isConstructorLike) (term configuration)
