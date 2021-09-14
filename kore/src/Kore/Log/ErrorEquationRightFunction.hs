{- |
Copyright : (c) Runtime Verification 2021
License   : BSD-3-Clause
-}
module Kore.Log.ErrorEquationRightFunction (
    ErrorEquationRightFunction (..),
    errorEquationRightFunction,
) where

import Control.Monad.Catch (
    Exception (..),
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Axiom (
    Axiom (..),
 )
import Kore.Equation.Equation (
    Equation (..),
 )
import Kore.Internal.TermLike (
    VariableName,
 )
import Log (
    Entry (..),
    MonadLog,
    Severity (Error),
    SomeEntry (SomeEntry),
    logError,
 )
import Prelude.Kore
import Pretty (
    Pretty,
    indent,
    layoutOneLine,
    pretty,
    renderText,
    vsep,
 )
import SQL (
    Table,
 )

-- | Error when RHS of equation is not a function pattern.
newtype ErrorEquationRightFunction = ErrorEquationRightFunction
    { equation :: Equation VariableName
    }
    deriving stock (Show, GHC.Generic)

instance SOP.Generic ErrorEquationRightFunction

instance SOP.HasDatatypeInfo ErrorEquationRightFunction

instance Pretty ErrorEquationRightFunction where
    pretty ErrorEquationRightFunction{equation} =
        vsep
            [ "Checking equation"
            , indent 4 $ pretty equation
            , "right-hand side is not a function pattern."
            ]

instance Exception ErrorEquationRightFunction where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorEquationRightFunction where
    entrySeverity _ = Error
    oneLineDoc
        ( ErrorEquationRightFunction
                Equation{attributes = Axiom{sourceLocation}}
            ) =
            pretty sourceLocation
    helpDoc _ = "errors raised when right-hand side of equation is not a function pattern"

instance SQL.Table ErrorEquationRightFunction

-- | Error when RHS of equation is not a function pattern.
errorEquationRightFunction ::
    MonadLog m =>
    Equation VariableName ->
    m ()
errorEquationRightFunction =
    logError . renderText . layoutOneLine . pretty . ErrorEquationRightFunction
