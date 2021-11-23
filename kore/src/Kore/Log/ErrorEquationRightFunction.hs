{- |
Copyright : (c) Runtime Verification 2021
License   : BSD-3-Clause
-}
module Kore.Log.ErrorEquationRightFunction (
    ErrorEquationRightFunction (..),
    errorEquationRightFunction,
) where

import Control.Exception (
    Exception (..),
    throw,
 )
import Control.Monad (
    (>=>),
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
    indent,
    pretty,
    vsep,
 )

--import SQL (
--    Table,
-- )

-- | Error when RHS of equation is not a function pattern.
newtype ErrorEquationRightFunction = ErrorEquationRightFunction
    { unErrorEquationRightFunction :: NonEmpty (Equation RewritingVariableName)
    }
    deriving stock (Show, GHC.Generic)

instance SOP.Generic ErrorEquationRightFunction

instance SOP.HasDatatypeInfo ErrorEquationRightFunction

instance Pretty ErrorEquationRightFunction where
    pretty =
        vsep . map prettyEqn . NonEmpty.toList . unErrorEquationRightFunction
      where
        prettyEqn eqn =
            vsep
                [ "Checking equation"
                , pretty $ sourceLocation $ attributes eqn
                , indent 4 $ pretty eqn
                , "right-hand side is not a function pattern."
                ]

instance Exception ErrorEquationRightFunction where
    toException = toException . SomeEntry
    fromException = fromException >=> fromEntry

instance Entry ErrorEquationRightFunction where
    entrySeverity _ = Error

    oneLineDoc (ErrorEquationRightFunction eqns) =
        NonEmpty.toList eqns
            & map (pretty . sourceLocation . attributes)
            & vsep
    helpDoc _ = "errors raised when right-hand side of equation is not a function pattern"

-- instance SQL.Table ErrorEquationRightFunction

-- | Error when RHS of equation is not a function pattern.
errorEquationRightFunction :: NonEmpty (Equation RewritingVariableName) -> m ()
errorEquationRightFunction = throw . ErrorEquationRightFunction
