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
    ( PureMLPatternSimplifier (..)
    , CommonPureMLPatternSimplifier
    , SimplificationProof (..)
    ) where

import Kore.AST.Common
       ( Variable )
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
newtype PureMLPatternSimplifier level variable =
    PureMLPatternSimplifier
        ( PureMLPattern level variable
        -> IntCounter
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

{-| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
-}
type CommonPureMLPatternSimplifier level =
    PureMLPatternSimplifier level Variable
