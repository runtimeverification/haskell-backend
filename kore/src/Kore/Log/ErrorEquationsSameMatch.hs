{- |
Copyright : (c) Runtime Verification 2021
License   : BSD-3-Clause
-}
module Kore.Log.ErrorEquationsSameMatch (
    ErrorEquationsSameMatch (..),
    errorEquationsSameMatch,
) where

import Control.Exception (
    Exception (..),
    throw,
 )
import qualified Data.List.NonEmpty as NonEmpty (
    toList,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Axiom (
    Axiom (..),
 )
import Kore.Equation.Equation (
    Equation (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Log (
    Entry (..),
    Severity (Error),
    SomeEntry (SomeEntry),
 )
import Prelude.Kore
import Pretty (
    Pretty,
    comma,
    hsep,
    indent,
    pretty,
    vsep,
 )

-- import SQL (
--    Table,
-- )

-- | Error when two equations both match a term.
newtype ErrorEquationsSameMatch = ErrorEquationsSameMatch
    { unErrorEquationsSameMatch ::
        NonEmpty
            ( Equation RewritingVariableName
            , Equation RewritingVariableName
            )
    }
    deriving stock (Show, GHC.Generic)

instance SOP.Generic ErrorEquationsSameMatch

instance SOP.HasDatatypeInfo ErrorEquationsSameMatch

instance Pretty ErrorEquationsSameMatch where
    pretty e = vsep ("Matching equation(s):" : prettyMatches)
      where
        prettyMatches =
            unErrorEquationsSameMatch e
                & NonEmpty.toList
                & map prettyMatch
        prettyMatch (eq1, eq2) =
            vsep
                [ "Equations"
                , indent 4 $ pretty eq1
                , "and"
                , indent 4 $ pretty eq2
                , "match the same term."
                ]

instance Exception ErrorEquationsSameMatch where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorEquationsSameMatch where
    entrySeverity _ = Error
    helpDoc _ =
        "errors raised when two equations from a\
        \ function definition can match the same term"
    oneLineDoc (ErrorEquationsSameMatch matches) =
        NonEmpty.toList matches
            & map prettySrcLoc
            & vsep
      where
        prettySrcLoc (eq1, eq2) =
            let srcLoc1 = sourceLocation $ attributes eq1
                srcLoc2 = sourceLocation $ attributes eq2
             in Pretty.hsep
                    [ pretty srcLoc1
                    , Pretty.comma
                    , pretty srcLoc2
                    ]

-- instance SQL.Table ErrorEquationsSameMatch

errorEquationsSameMatch ::
    NonEmpty (Equation RewritingVariableName, Equation RewritingVariableName) ->
    m ()
errorEquationsSameMatch = throw . ErrorEquationsSameMatch
