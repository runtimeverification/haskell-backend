{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewritesInstantiation
    ( ErrorRewritesInstantiation (..)
    , errorRewritesInstantiation
    ) where

import Prelude.Kore

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
import Kore.Internal.Variable
    ( InternalVariable
    , Variable
    , toVariable
    )
import Kore.Step.Step
    ( UnifiedRule
    )
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern (..)
    , rewriteRuleToTerm
    )
import Kore.Unification.Error
import Kore.Unparser
    ( unparse
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
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
