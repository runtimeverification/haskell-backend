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

import qualified Control.Monad as Monad
import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import qualified Control.Monad.Except as Except
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
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern


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

type PatternMap = Map (CommonPurePattern Object) (CommonPurePattern Object)

{- | Abort function evaluation if the argument is not a Map domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicatible'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinDomainMap
    :: Monad m
    => String  -- ^ Context for error message
    -> CommonPurePattern Object  -- ^ Operand pattern
    -> ExceptT (AttemptedFunction Object Kore.Variable) m PatternMap
expectBuiltinDomainMap ctx =
    \case
        Kore.DV_ _ domain ->
            case domain of
                Kore.BuiltinDomainMap _map -> return _map
                _ -> Builtin.verifierBug (ctx ++ ": Domain value is not a map")
        _ ->
            Except.throwError NotApplicable

getAttemptedFunction :: Monad m => ExceptT r m r -> m r
getAttemptedFunction = fmap (either id id) . runExceptT

returnMap
    :: Monad m
    => Kore.Sort Object
    -> PatternMap
    -> m (AttemptedFunction Object Kore.Variable)
returnMap resultSort _map =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ Kore.DV_ resultSort
        $ Kore.BuiltinDomainMap _map

evalLookup :: Builtin.Function
evalLookup =
    Builtin.functionEvaluator evalLookup0
  where
    evalLookup0 _ _ _ arguments =
        getAttemptedFunction
        (do
            let (_map, _key) =
                    case arguments of
                        [_map, _key] -> (_map, _key)
                        _ -> Builtin.wrongArity "MAP.lookup"
            _map <- expectBuiltinDomainMap "MAP.lookup" _map
            Builtin.appliedFunction
                $ maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern
                $ Map.lookup _key _map
        )

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ _ resultSort = \arguments ->
        case arguments of
            [_key, _value] -> returnMap resultSort (Map.singleton _key _value)
            _ -> Builtin.wrongArity "MAP.element"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0 _ _ resultSort = \arguments ->
        getAttemptedFunction
        (do
            let (_map1, _map2) =
                    case arguments of
                        [_map1, _map2] -> (_map1, _map2)
                        _ -> Builtin.wrongArity "MAP.concat"
            _map1 <- expectBuiltinDomainMap "MAP.concat" _map1
            _map2 <- expectBuiltinDomainMap "MAP.concat" _map2
            let overlapping =
                    (not . Set.null)
                    (Set.intersection (Map.keysSet _map1) (Map.keysSet _map2))
            -- Result is ‘\bottom{}()’ when there is overlap between the keys
            -- of the operands.
            (Monad.when overlapping . Except.throwError)
                (Applied $ OrOfExpandedPattern.make [ExpandedPattern.bottom])
            returnMap resultSort (Map.union _map1 _map2)
        )

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ _ resultSort =
        \case
            [] -> returnMap resultSort Map.empty
            _ -> Builtin.wrongArity "MAP.unit"

evalUpdate :: Builtin.Function
evalUpdate =
    Builtin.functionEvaluator evalUpdate0
  where
    evalUpdate0 _ _ resultSort = \arguments ->
        getAttemptedFunction
        (do
            let (_map, _key, _value) =
                    case arguments of
                        [_map, _key, _value] -> (_map, _key, _value)
                        _ -> Builtin.wrongArity "MAP.update"
            _map <- expectBuiltinDomainMap "MAP.update" _map
            returnMap resultSort (Map.insert _key _value _map)
        )

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
