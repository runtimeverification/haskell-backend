{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRuleMergeDuplicateId
    ( ErrorRuleMergeDuplicateIds
    , errorRuleMergeDuplicateIds
    ) where

import Prelude.Kore

import Control.Exception
    ( Exception (..)
    , throw
    )
import qualified Control.Lens as Lens
import Data.Generics.Product
    ( field
    )
import Data.Generics.Wrapped
    ( _Unwrapped
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.SourceLocation
    ( SourceLocation (..)
    )
import Kore.Internal.TermLike
    ( VariableName
    )
import Kore.Step.RulePattern
    ( RewriteRule (..)
    )
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

newtype ErrorRuleMergeDuplicateIds =
    ErrorRuleMergeDuplicateIds
        { unErrorRuleMergeDuplicateIds :: Map Text [SourceLocation]
        }
    deriving (Show)
    deriving (GHC.Generic)
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
        Map.foldMapWithKey accum duplicateIds
      where
        accum ruleId locations =
            Pretty.vsep
                $ ["The rules at the following locations:"]
                <> fmap (Pretty.indent 4 . pretty) locations
                <> [ Pretty.indent 2 "all have the following id:"
                   , Pretty.indent 4 (pretty ruleId)
                   ]

errorRuleMergeDuplicateIds :: Map Text [RewriteRule VariableName] -> a
errorRuleMergeDuplicateIds duplicateIds =
    throw (ErrorRuleMergeDuplicateIds idsWithlocations)
  where
    idsWithlocations =
        (fmap . fmap)
        (
            Lens.view
                ( _Unwrapped
                . field @"attributes"
                . field @"sourceLocation"
                )
        )
        duplicateIds
