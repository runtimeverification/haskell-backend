{- |
Copyright : (c) Runtime Verification, 2020-2021
License : BSD-3-Clause
-}
module Kore.Log.Error (
    -- * ErrorBottomTotalFunction
    ErrorBottomTotalFunction (..),
    errorBottomTotalFunction,

    -- * ErrorDecidePredicateUnknown
    ErrorDecidePredicateUnknown (..),
    errorDecidePredicateUnknown,

    -- * ErrorEquationRightFunction
    ErrorEquationRightFunction (..),
    errorEquationRightFunction,

    -- * ErrorEquationsSameMatch
    ErrorEquationsSameMatch (..),
    errorEquationsSameMatch,

    -- * ErrorException
    ErrorException,
    errorException,

    -- * ErrorParse
    ErrorParse (..),
    errorParse,

    -- * ErrorVerify
    ErrorVerify (..),
    errorVerify,
) where

import Control.Exception (
    AssertionFailed,
    throw,
 )
import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
    SomeException,
    fromException,
    throwM,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Axiom (
    Axiom (..),
 )
import Kore.Equation.Equation (
    Equation (..),
 )
import qualified Kore.Error as Kore
import Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    VariableName,
    toVariableName,
 )
import qualified Kore.Internal.TermLike as TermLike (
    mapVariables,
 )
import Kore.Unparser (
    unparse,
 )
import SQL (
    Table,
 )

-- cyclical dependency
--import Kore.Rewrite.AxiomPattern (
--    AxiomPattern,
--    getAxiomPattern,
-- )

-- cyclical dependency
-- import Kore.Rewrite.RulePattern (
--    RewriteRule (..),
-- )
import Kore.Validate.Error (
    VerifyError,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
    hsep,
    indent,
    layoutOneLine,
    prettyException,
    renderText,
    vsep,
 )
import qualified Pretty

-- | ErrorBottomTotalFunction
newtype ErrorBottomTotalFunction = ErrorBottomTotalFunction
    { term :: TermLike VariableName
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)

instance SOP.Generic ErrorBottomTotalFunction

instance SOP.HasDatatypeInfo ErrorBottomTotalFunction

instance Pretty ErrorBottomTotalFunction where
    pretty ErrorBottomTotalFunction{term} =
        Pretty.vsep
            [ "Evaluating total function"
            , Pretty.indent 4 (unparse term)
            , "has resulted in \\bottom."
            ]

instance Exception ErrorBottomTotalFunction where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Entry ErrorBottomTotalFunction where
    entrySeverity _ = Error
    oneLineDoc _ = "ErrorBottomTotalFunction"
    helpDoc _ = "errors raised when a total function is undefined"

instance SQL.Table ErrorBottomTotalFunction

errorBottomTotalFunction ::
    MonadThrow logger =>
    InternalVariable variable =>
    TermLike variable ->
    logger ()
errorBottomTotalFunction (TermLike.mapVariables (pure toVariableName) -> term) =
    throwM ErrorBottomTotalFunction{term}

-- | ErrorDecidePredicateUnknown
newtype ErrorDecidePredicateUnknown = ErrorDecidePredicateUnknown
    { predicates :: NonEmpty (Predicate VariableName)
    }
    deriving stock (Show)

instance Exception ErrorDecidePredicateUnknown where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Pretty ErrorDecidePredicateUnknown where
    pretty ErrorDecidePredicateUnknown{predicates} =
        Pretty.vsep
            ( [ "Failed to decide predicate:"
              , Pretty.indent 4 (pretty predicate)
              ]
                ++ do
                    sideCondition <- sideConditions
                    [ "with side condition:"
                        , Pretty.indent 4 (pretty sideCondition)
                        ]
            )
      where
        predicate :| sideConditions = predicates

instance Entry ErrorDecidePredicateUnknown where
    entrySeverity _ = Error
    oneLineDoc _ = "ErrorDecidePredicateUnknown"
    helpDoc _ =
        "errors raised when the solver cannot decide satisfiability of a formula"

errorDecidePredicateUnknown ::
    InternalVariable variable =>
    NonEmpty (Predicate variable) ->
    log a
errorDecidePredicateUnknown predicates' =
    throw ErrorDecidePredicateUnknown{predicates}
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'

{- | ErrorEquationRightFunction
 Error when RHS of equation is not a function pattern.
-}
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

{- | ErrorEquationsSameMatch
 Error when two equations both match a term.
-}
data ErrorEquationsSameMatch = ErrorEquationsSameMatch
    { equation1, equation2 :: Equation VariableName
    }
    deriving stock (Show, GHC.Generic)

instance SOP.Generic ErrorEquationsSameMatch

instance SOP.HasDatatypeInfo ErrorEquationsSameMatch

instance Pretty ErrorEquationsSameMatch where
    pretty ErrorEquationsSameMatch{equation1, equation2} =
        vsep
            [ "Equations"
            , indent 4 $ pretty equation1
            , "and"
            , indent 4 $ pretty equation2
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
    oneLineDoc
        ( ErrorEquationsSameMatch
                Equation{attributes = Axiom{sourceLocation = sourceLoc1}}
                Equation{attributes = Axiom{sourceLocation = sourceLoc2}}
            ) =
            Pretty.hsep
                [ pretty sourceLoc1
                , Pretty.comma
                , pretty sourceLoc2
                ]

instance SQL.Table ErrorEquationsSameMatch

errorEquationsSameMatch ::
    MonadLog m =>
    Equation VariableName ->
    Equation VariableName ->
    m ()
errorEquationsSameMatch eq1 eq2 =
    logError . renderText . layoutOneLine . pretty $
        ErrorEquationsSameMatch eq1 eq2

-- | ErrorException
newtype ErrorException = ErrorException {getException :: SomeException}
    deriving stock (Show)

instance Pretty ErrorException where
    pretty (ErrorException someException) =
        (vsep . catMaybes)
            [ Just $ prettyException someException
            , pleaseFileBugReport
            ]
      where
        pleaseFileBugReport = do
            _ <- fromException someException :: Maybe AssertionFailed
            (pure . hsep)
                [ "Please file a bug report:"
                , "https://github.com/kframework/kore/issues"
                ]

instance Entry ErrorException where
    entrySeverity _ = Error
    oneLineDoc _ = "ErrorException"
    helpDoc _ = "log internal errors"

errorException :: MonadLog log => SomeException -> log ()
errorException = logEntry . ErrorException

-- | ErrorParse
newtype ErrorParse = ErrorParse {message :: String}
    deriving stock (Show)

instance Exception ErrorParse where
    toException = toException . SomeEntry
    fromException exn = fromException exn >>= fromEntry
    displayException = message

instance Pretty ErrorParse where
    pretty ErrorParse{message} =
        Pretty.pretty message

instance Entry ErrorParse where
    entrySeverity _ = Error
    oneLineDoc _ = "ErrorParse"

errorParse :: MonadThrow log => String -> log a
errorParse message =
    throwM ErrorParse{message}

-- | ErrorVerify
newtype ErrorVerify = ErrorVerify {koreError :: Kore.Error VerifyError}
    deriving stock (Show)

instance Exception ErrorVerify where
    toException = toException . SomeEntry
    fromException exn = fromException exn >>= fromEntry
    displayException = Kore.printError . koreError

instance Pretty ErrorVerify where
    pretty ErrorVerify{koreError} =
        Pretty.pretty (Kore.printError koreError)

instance Entry ErrorVerify where
    entrySeverity _ = Error
    oneLineDoc _ = "ErrorVerify"

errorVerify :: MonadThrow log => Kore.Error VerifyError -> log a
errorVerify koreError =
    throwM ErrorVerify{koreError}
