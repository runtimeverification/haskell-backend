{-|
Module      : Kore.Step.Function.Data
Description : Data structures used for function evaluation.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Data
    (  ApplicationFunctionEvaluator (..)
    , CommonApplicationFunctionEvaluator
    , AttemptedFunction (..)
    , CommonAttemptedFunction
    , notApplicableFunctionEvaluator
    , purePatternFunctionEvaluator
    ) where

import Kore.AST.Common
       ( Application, Variable )
import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern, makeFromSinglePurePattern )
import Kore.Step.Simplification.Data
       ( PureMLPatternSimplifier, Simplifier,
       SimplificationProof (..) )
import Kore.Step.StepperAttributes
       ( StepperAttributes )

{-| 'ApplicationFunctionEvaluator' evaluates functions on an 'Application'
pattern. This can be either a built-in evaluator or a user-defined one.

Arguments:

* 'MetadataTools' are tools for finding additional information about
patterns such as their sorts, whether they are constructors or hooked.

* 'PureMLPatternSimplifier' is a Function for simplifying patterns, used for
the post-processing of the function application results.

* 'Application' is the pattern to be evaluated.

Return value:

It returns the result of appling the function, together with a proof certifying
that the function was applied correctly (which is only a placeholder right now).
-}
newtype ApplicationFunctionEvaluator level domain variable =
    ApplicationFunctionEvaluator
        (forall . ( MetaOrObject level)
        => MetadataTools level StepperAttributes
        -> PureMLPatternSimplifier level domain variable
        -> Application level (PureMLPattern level domain variable)
        -> Simplifier
            ( AttemptedFunction level domain variable
            , SimplificationProof level
            )
        )

{-| 'CommonApplicationFunctionEvaluator' particularizes
'ApplicationFunctionEvaluator' to 'Variable', following the same pattern as
the other `Common*` types.
-}
type CommonApplicationFunctionEvaluator level domain =
    ApplicationFunctionEvaluator level domain Variable

{-| 'AttemptedFunction' is a generalized 'FunctionResult' that handles
cases where the function can't be fully evaluated.
-}
data AttemptedFunction level domain variable
    = NotApplicable
    | Applied !(OrOfExpandedPattern level domain variable)
  deriving (Show, Eq)

{-| 'CommonAttemptedFunction' particularizes 'AttemptedFunction' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedFunction level domain = AttemptedFunction level domain Variable

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableFunctionEvaluator
    :: Simplifier
         (AttemptedFunction level1 domain variable, SimplificationProof level2)
notApplicableFunctionEvaluator = pure (NotApplicable, SimplificationProof)

-- |Yields a pure 'Simplifier' which produces a given 'PureMLPattern'
purePatternFunctionEvaluator
    :: (MetaOrObject level)
    => PureMLPattern level domain variable
    -> Simplifier (AttemptedFunction level domain variable, SimplificationProof level')
purePatternFunctionEvaluator p =
    pure
        (Applied (makeFromSinglePurePattern p)
        , SimplificationProof
        )

