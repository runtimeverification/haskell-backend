{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause
-}
module Kore.CheckFunctions (
    checkFunctions,
) where

import Control.Monad (
    foldM,
 )
import qualified Data.Text as Text
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.BugReport (
    ExitCode (ExitFailure, ExitSuccess),
 )
import Kore.Equation (
    Equation (Equation),
    extractEquations,
    right,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    isFunctionPattern,
 )
import Log (
    MonadLog,
    logError,
 )
import Prelude.Kore
import Pretty (
    layoutOneLine,
    pretty,
    renderText,
    (<+>),
 )

checkFunctions ::
    MonadLog m =>
    VerifiedModule StepperAttributes ->
    m ExitCode
checkFunctions verifiedModule =
    foldM equationMap ExitSuccess $ extractEquations verifiedModule
  where
    equationMap status eqns = case status of
        ExitSuccess -> foldM checkEquation ExitSuccess eqns
        failure -> return failure

checkEquation ::
    MonadLog m =>
    InternalVariable variable =>
    ExitCode ->
    Equation variable ->
    m ExitCode
checkEquation failure@(ExitFailure _) _ = return failure
checkEquation _ eqn@Equation{right}
    | isFunctionPattern right = return ExitSuccess
    | otherwise = do
        logError $ renderText $ layoutOneLine err
        return $ ExitFailure 3
  where
    err =
        pretty (Text.pack "RHS of equation is not a function pattern:")
            <+> pretty eqn
