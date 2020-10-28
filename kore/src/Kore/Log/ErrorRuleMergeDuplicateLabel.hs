{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRuleMergeDuplicateLabel
    ( ErrorRuleMergeDuplicateLabel
    , errorRuleMergeDuplicateLabel
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

data ErrorRuleMergeDuplicateLabel =
    ErrorRuleMergeDuplicateLabel
        { locations :: [SourceLocation]
        , ruleLabel :: Text
        }
    deriving (Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Exception ErrorRuleMergeDuplicateLabel where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorRuleMergeDuplicateLabel where
    entrySeverity _ = Error
    helpDoc _ =
        "error thrown during rule merging when\
        \ multiple rules have the same label"

instance Pretty ErrorRuleMergeDuplicateLabel where
    pretty ErrorRuleMergeDuplicateLabel { locations , ruleLabel } =
        Pretty.vsep
            $ ["The rules at the following locations:"]
            <> fmap (Pretty.indent 4 . pretty) locations
            <> [ Pretty.indent 2 "all have the following label:"
               , Pretty.indent 4 (pretty ruleLabel)
               ]

errorRuleMergeDuplicateLabel :: [RewriteRule VariableName] -> Text -> a
errorRuleMergeDuplicateLabel rules ruleLabel =
    throw ErrorRuleMergeDuplicateLabel { locations, ruleLabel }
  where
    locations =
        Lens.view
            ( _Unwrapped
            . field @"attributes"
            . field @"sourceLocation"
            )
        <$> rules
