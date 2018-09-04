{- |
Module      : Kore.Builtin.KEqual
Description : Built-in KEQUAL operations
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
                 ( Application(..), Variable (..) )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( PureMLPattern )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Error
                 ( unificationToStepError )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..), AttemptedFunction (..),
                 notApplicableFunctionEvaluator, purePatternFunctionEvaluator )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier, SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Unifier
                 ( unificationProcedure )

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

{- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
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
    -> Application Object (PureMLPattern Object domain Variable)
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
    evalEq resultSort t1 t2 =
        case unificationProcedure tools t1 t2 of
            Right (subst, predicate, _)
                | Predicate.isFalse predicate ->
                    purePatternFunctionEvaluator
                        (Bool.asPattern resultSort false)
                | null subst ->
                    purePatternFunctionEvaluator
                        (Bool.asPattern resultSort true)
                | otherwise -> notApplicableFunctionEvaluator
            Left err -> case unificationToStepError () (Left err) of
                Right () ->
                    purePatternFunctionEvaluator
                        (Bool.asPattern resultSort false)
                Left _ -> notApplicableFunctionEvaluator
