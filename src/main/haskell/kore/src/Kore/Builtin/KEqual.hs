{- |
Module      : Kore.Builtin.KEqual
Description : Built-in KEQUAL operations
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.KEqual as KEqual
@
 -}
module Kore.Builtin.KEqual
    ( symbolVerifiers
    , builtinFunctions
    ) where

import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Application (..), PureMLPattern, Variable (..) )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..), AttemptedFunction (..),
                 notApplicableFunctionEvaluator, purePatternFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier, SimplificationProof (..),
                 Simplifier )
import qualified Kore.Step.Simplification.Equals as Equals
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( "KEQUAL.eq"
      , Builtin.verifySymbol Bool.assertSort [trivialVerifier, trivialVerifier])
    , ("KEQUAL.neq"
      , Builtin.verifySymbol Bool.assertSort [trivialVerifier, trivialVerifier])
    ]
  where
    trivialVerifier :: Builtin.SortVerifier
    trivialVerifier = const $ const $ Right ()

{- | @builtinFunctions@ defines the hooks for @KEQUAL.eq@ and @KEQUAL.neq@
which can take arbitrary terms (of the same sort) and check whether they are
equal or not, producing a builtin boolean value.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
    [ ("KEQUAL.eq", ApplicationFunctionEvaluator (evalKEq True False))
    , ("KEQUAL.neq", ApplicationFunctionEvaluator (evalKEq False True))
    ]

evalKEq
    :: Bool
    -> Bool
    -> MetadataTools.MetadataTools Object StepperAttributes
    -> PureMLPatternSimplifier Object Variable
    -> Application Object (PureMLPattern Object Variable)
    -> Simplifier
        ( AttemptedFunction Object Variable
        , SimplificationProof Object
        )
evalKEq true false tools _ pat =
    case pat of
        Application
            { applicationSymbolOrAlias =
                (MetadataTools.getResultSort tools -> resultSort)
            , applicationChildren = [t1, t2]
            } -> evalEq resultSort t1 t2
        _ -> notApplicableFunctionEvaluator
  where
    evalEq resultSort t1 t2 = do
        (result, _proof) <- Equals.makeEvaluate tools ep1 ep2
        if OrOfExpandedPattern.isTrue result
            then purePatternFunctionEvaluator (Bool.asPattern resultSort true)
        else if OrOfExpandedPattern.isFalse result
            then purePatternFunctionEvaluator (Bool.asPattern resultSort false)
        else notApplicableFunctionEvaluator
      where
        ep1 = ExpandedPattern.fromPurePattern t1
        ep2 = ExpandedPattern.fromPurePattern t2
