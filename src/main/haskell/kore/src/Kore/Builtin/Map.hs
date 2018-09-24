{- |
Module      : Kore.Builtin.Map
Description : Built-in arbitrary-precision integer sort
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Map as Map
@
 -}
module Kore.Builtin.Map
    ( sort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    ) where

import qualified Data.HashMap.Strict as HashMap
import           Data.Map

import           Kore.AST.Common
                 ( Application (..), SymbolOrAlias )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_ )
import qualified Kore.Builtin.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( Hook (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..),
                 notApplicableFunctionEvaluator, purePatternFunctionEvaluator )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )


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
          [ assertSort
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
    hook (symAttributes tools sym) == Hook (Just hookName)

evalBind :: Builtin.Function
evalBind =
    ApplicationFunctionEvaluator evalBind0
  where
    evalBind0 _ _ _ = notApplicableFunctionEvaluator

-- FIXME: proper equality modulo alpha?
evalLookup :: Builtin.Function
evalLookup =
    ApplicationFunctionEvaluator evalLookup0
  where
    evalLookup0 tools _ pat =
          case pat of
              Application _ [m, k] -> goFind k m
              _ -> notApplicableFunctionEvaluator
      where
        goFind k m = case m of
            App_ h [k', v]
              | isHook tools h "MAP.element" ->
                  if k == k'
                      then purePatternFunctionEvaluator v
                      else notApplicableFunctionEvaluator
            App_ h [k', v, m']
              | isHook tools h "MAP.bind" ->
                  if k == k'
                      then purePatternFunctionEvaluator v
                      else goFind k m'
            _ -> notApplicableFunctionEvaluator


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
