{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorRewriteLoop
    ( ErrorRewriteLoop
    , errorRewriteLoop
    ) where

import Prelude.Kore

import Control.Exception
    ( Exception (..)
    , throw
    )
import GHC.Exception
    ( prettyCallStackLines
    )
import GHC.Stack
    ( CallStack
    , callStack
    )

import Kore.Attribute.Axiom
    ( Axiom (..)
    )
import Kore.Step.RulePattern
    ( RewriteRule
    , RulePattern (..)
    , getRewriteRule
    )
import Kore.Syntax.Variable
    ( VariableName
    )
import Pretty

import Log

data ErrorRewriteLoop =
    ErrorRewriteLoop
        { rule :: !(RewriteRule VariableName)
        , errorCallStack :: !CallStack
        }
    deriving (Show)

instance Exception ErrorRewriteLoop where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Pretty ErrorRewriteLoop where
    pretty ErrorRewriteLoop { rule, errorCallStack } =
        Pretty.vsep $
            [ "Found semantic rule with the same left- and right-hand side at:"
            , Pretty.pretty
                . sourceLocation . attributes . getRewriteRule $ rule
            , "Execution would not terminate when the rule applies."
            ]
            <> fmap Pretty.pretty (prettyCallStackLines errorCallStack)

instance Entry ErrorRewriteLoop where
    entrySeverity _ = Error

errorRewriteLoop
    :: HasCallStack
    => RewriteRule VariableName
    -> log a
errorRewriteLoop rule =
    throw ErrorRewriteLoop { rule, errorCallStack = callStack }
