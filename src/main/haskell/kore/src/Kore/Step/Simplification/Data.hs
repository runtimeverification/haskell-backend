{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Data
    ( SimplificationError
    , Simplifier
    , evalSimplifier
    , PureMLPatternSimplifier (..)
    , CommonPureMLPatternSimplifier
    , SimplificationProof (..)
    ) where

import Control.Monad.Except
       ( ExceptT, runExceptT )

import Kore.AST.Common
       ( Variable )
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.Error
       ( Error )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter, runIntCounter )


{- | A tag for errors during simplification

  See also: 'Error'

 -}
data SimplificationError

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

{- | The concrete monad in which simplification occurs.

 -}
-- TODO (thomas.tuegel): Replace IntCounter with a single state carrying both
-- the counter and the proof.
-- TODO (thomas.tuegel): Lift the StateT to the outer level.
type Simplifier = ExceptT (Error SimplificationError) IntCounter

{- | Evaluate a simplifier computation.

  Only the result (or error) is returned. The 'IntCounter' is discarded.

  -}
evalSimplifier :: Simplifier a -> Either (Error SimplificationError) a
evalSimplifier simp =
    let
        (result, _) = runIntCounter (runExceptT simp) 0
    in
      result

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
newtype PureMLPatternSimplifier level variable =
    PureMLPatternSimplifier
        ( PureMLPattern level domain variable
        -> Simplifier
            ( OrOfExpandedPattern level domain variable
            , SimplificationProof level
            )
        )

{-| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
-}
type CommonPureMLPatternSimplifier level =
    PureMLPatternSimplifier level Variable
