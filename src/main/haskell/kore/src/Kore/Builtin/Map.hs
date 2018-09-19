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
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Step.ExpandedPattern as ExpandedPattern


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
    [ ( "MAP.concat"
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( "MAP.element"
      , Builtin.verifySymbol assertSort [anySort, anySort]
      )
    , ( "MAP.lookup"
      , Builtin.verifySymbol anySort [assertSort, anySort]
      )
    , ( "MAP.unit"
      , Builtin.verifySymbol assertSort []
      )
    , ( "MAP.update"
      , Builtin.verifySymbol assertSort [assertSort, anySort, anySort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

expectBuiltinDomainMap
    :: CommonPurePattern Object
    -> Map (CommonPurePattern Object) (CommonPurePattern Object)
expectBuiltinDomainMap =
    \case
        Kore.DV_ _ dom ->
            case dom of
                Kore.BuiltinDomainMap m -> m
                _ -> error "Expected a MAP.Map builtin domain value"
        _ ->
            error "Expected a domain value"

evalLookup :: Builtin.Function
evalLookup =
    Builtin.functionEvaluator evalLookup0
  where
    evalLookup0 _ _ _ =
        \case
            [expectBuiltinDomainMap -> m, k] ->
                Builtin.appliedFunction
                $ maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern
                $ Map.lookup k m
            _ -> Builtin.wrongArity "MAP.lookup"

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ _ s =
        \case
            [k, v] ->
                Builtin.appliedFunction
                $ ExpandedPattern.fromPurePattern
                $ Kore.DV_ s $ Kore.BuiltinDomainMap $ Map.singleton k v
            _ -> Builtin.wrongArity "MAP.element"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0 _ _ s =
        \case
            [expectBuiltinDomainMap -> m1, expectBuiltinDomainMap -> m2]
                | overlapping -> Builtin.appliedFunction ExpandedPattern.bottom
                | otherwise ->
                    Builtin.appliedFunction
                    $ ExpandedPattern.fromPurePattern
                    $ Kore.DV_ s $ Kore.BuiltinDomainMap $ Map.union m1 m2
              where
                overlapping =
                    (not . Set.null)
                    (Set.intersection (Map.keysSet m1) (Map.keysSet m2))
            _ -> Builtin.wrongArity "MAP.concat"

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ _ s =
        \case
            [] ->
                Builtin.appliedFunction
                $ ExpandedPattern.fromPurePattern
                $ Kore.DV_ s $ Kore.BuiltinDomainMap $ Map.empty
            _ ->
                Builtin.wrongArity "MAP.unit"

evalUpdate :: Builtin.Function
evalUpdate =
    Builtin.functionEvaluator evalUpdate0
  where
    evalUpdate0 _ _ s =
        \case
            [expectBuiltinDomainMap -> m, k, v] ->
                Builtin.appliedFunction
                $ ExpandedPattern.fromPurePattern
                $ Kore.DV_ s $ Kore.BuiltinDomainMap $ Map.insert k v m
            _ -> Builtin.wrongArity "MAP.element"

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
        [ ("MAP.concat", evalConcat)
        , ("MAP.lookup", evalLookup)
        , ("MAP.element", evalElement)
        , ("MAP.unit", evalUnit)
        , ("MAP.update", evalUpdate)
        ]
