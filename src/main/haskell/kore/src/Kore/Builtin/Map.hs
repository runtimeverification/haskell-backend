{- |
Module      : Kore.Builtin.Map
Description : Built-in arbitrary-precision integer sort
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Int as Int
@
 -}
module Kore.Builtin.Map
    ( sort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    ) where

import           Control.Monad
                 ( void )
import           Data.Functor.Foldable
import           Data.Map
import qualified Data.HashMap.Strict as HashMap
import qualified Text.Megaparsec.Char.Lexer as Parsec

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML

import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTUtils.SmartConstructors

import           Kore.IndexedModule.MetadataTools

import           Kore.Variables.Fresh.IntCounter 
 ( IntCounter )

import           Kore.Step.Function.Data
import           Kore.Step.StepperAttributes
import           Kore.Step.ExpandedPattern
import           Kore.Predicate.Predicate
import           Kore.Step.OrOfExpandedPattern

import           Kore.Builtin.Hook
import qualified Kore.Builtin.Builtin as Builtin

import Kore.Step.Simplification.Data


{- | Builtin name of the @Map@ sort.
 -}
sort :: String
sort = "MAP.Map"

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort findSort = Builtin.verifySort findSort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [
      ("MAP.bind" 
      , Builtin.verifySymbol trivialVerifier 
          [ trivialVerifier
          , trivialVerifier
          , trivialVerifier
          ]
      )
    , ("MAP.emp"
      , Builtin.verifySymbol trivialVerifier 
          [ trivialVerifier
          , trivialVerifier
          , trivialVerifier
          ]
      )
    , ("MAP.merge"
      , Builtin.verifySymbol trivialVerifier
          [ trivialVerifier
          , trivialVerifier
          ]
      )
    , ("MAP.element"
      , Builtin.verifySymbol trivialVerifier
          [ trivialVerifier
          , trivialVerifier
          ]
      )
    , ("MAP.lookup"
      , Builtin.verifySymbol trivialVerifier
          [ trivialVerifier
          , trivialVerifier
          , trivialVerifier
          ]
      )
    ]
  where 
    trivialVerifier :: Builtin.SortVerifier
    trivialVerifier = const $ const $ Right ()

isHook 
    :: MetadataTools Object StepperAttributes
    -> SymbolOrAlias Object
    -> String
    -> Bool
isHook tools sym hookName = 
    hook (attributes tools sym) == Hook (Just hookName)

trivialExpandedPattern
    :: MetaOrObject level 
    => PureMLPattern level var 
    -> ExpandedPattern level var
trivialExpandedPattern p = 
    ExpandedPattern p makeTruePredicate []

trivialEvalResult
    :: (Applicative f, MetaOrObject level1) 
    => PureMLPattern level1 variable
    -> f (AttemptedFunction level1 variable, SimplificationProof level2)
trivialEvalResult p = 
    pure (Applied (MultiOr [trivialExpandedPattern p]), SimplificationProof)

failedToEval
    :: Simplifier 
         (AttemptedFunction level1 variable, SimplificationProof level2)
failedToEval = pure (NotApplicable, SimplificationProof)

evalElement :: Builtin.Function
evalElement = 
    ApplicationFunctionEvaluator evalElement0
  where
    evalElement0 tools contEval pat = 
      trivialEvalResult (Fix $ ApplicationPattern pat) 

evalBind :: Builtin.Function
evalBind =
    ApplicationFunctionEvaluator evalBind0
  where
    evalBind0 tools contEval pat = 
      case pat of
        Application h [k, v, m]
         | hook (attributes tools h) == Hook (Just "MAP.bind") ->  failedToEval
        _ -> failedToEval

evalMerge :: Builtin.Function
evalMerge = 
    ApplicationFunctionEvaluator evalMerge0
  where
    evalMerge0 tools contEval pat = 
      case pat of
        Application h [m1, m2]
         | isHook tools h "MAP.merge" -> trivialEvalResult $  goMerge m1 m2
      where 
        goMerge m1 m2 = undefined

-- FIXME: proper equality modulo alpha?
evalLookup :: Builtin.Function
evalLookup = 
    ApplicationFunctionEvaluator evalLookup0
  where
    evalLookup0 tools contEval pat = 
      case pat of
        Application h [k, m]
         | hook (attributes tools h) == Hook (Just "MAP.lookup") -> goFind k m
        _ -> failedToEval
      where 
        goFind k m = case m of
          App_ h [k', v]
           | isHook tools h "MAP.element" -> 
              if k == k'
                then trivialEvalResult v 
                else failedToEval
          App_ h [k', v, m']
           | isHook tools h "MAP.bind" -> 
              if k == k' 
                then trivialEvalResult v
                else goFind k m'


{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions = 
  fromList
    [
      ("MAP.bind", evalBind)
    , ("MAP.lookup", evalLookup)
    , ("MAP.element", Builtin.notImplemented)
    ]
