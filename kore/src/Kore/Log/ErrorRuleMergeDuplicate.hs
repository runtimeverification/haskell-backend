{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.ErrorRuleMergeDuplicate (
    ErrorRuleMergeDuplicateIds,
    errorRuleMergeDuplicateIds,
    ErrorRuleMergeDuplicateLabels,
    errorRuleMergeDuplicateLabels,
) where

import Control.Exception (
    Exception (..),
    throw,
 )
import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Generics.Wrapped (
    _Unwrapped,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.SourceLocation (
    SourceLocation (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

newtype ErrorRuleMergeDuplicateIds = ErrorRuleMergeDuplicateIds
    { unErrorRuleMergeDuplicateIds :: Map Text [SourceLocation]
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Exception ErrorRuleMergeDuplicateIds where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorRuleMergeDuplicateIds where
    entrySeverity _ = Error
    helpDoc _ =
        "error thrown during rule merging when\
        \ multiple rules have the same id"

instance Pretty ErrorRuleMergeDuplicateIds where
    pretty (ErrorRuleMergeDuplicateIds duplicateIds) =
        prettyErrorText "id" duplicateIds

newtype ErrorRuleMergeDuplicateLabels = ErrorRuleMergeDuplicateLabels
    { unErrorRuleMergeDuplicateLabels :: Map Text [SourceLocation]
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Exception ErrorRuleMergeDuplicateLabels where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorRuleMergeDuplicateLabels where
    entrySeverity _ = Error
    helpDoc _ =
        "error thrown during rule merging when\
        \ multiple rules have the same label"

instance Pretty ErrorRuleMergeDuplicateLabels where
    pretty (ErrorRuleMergeDuplicateLabels duplicateLabels) =
        prettyErrorText "label" duplicateLabels

errorRuleMergeDuplicateIds :: Map Text [RewriteRule RewritingVariableName] -> a
errorRuleMergeDuplicateIds (getLocations -> duplicateIds) =
    throw (ErrorRuleMergeDuplicateIds duplicateIds)

errorRuleMergeDuplicateLabels :: Map Text [RewriteRule RewritingVariableName] -> a
errorRuleMergeDuplicateLabels (getLocations -> duplicateLabels) =
    throw (ErrorRuleMergeDuplicateLabels duplicateLabels)

prettyErrorText :: Text -> Map Text [SourceLocation] -> Pretty.Doc ann
prettyErrorText type' = Map.foldMapWithKey accum
  where
    accum name locations =
        Pretty.vsep $
            ["The rules at the following locations:"]
                <> fmap (Pretty.indent 4 . pretty) locations
                <> [ Pretty.indent 2 duplicateNameType
                   , Pretty.indent 4 (pretty name)
                   ]
    duplicateNameType =
        Pretty.hsep ["all have the following", pretty type', ":"]

getLocations :: Map Text [RewriteRule RewritingVariableName] -> Map Text [SourceLocation]
getLocations =
    (fmap . fmap)
        ( Lens.view
            ( _Unwrapped
                . field @"attributes"
                . field @"sourceLocation"
            )
        )
