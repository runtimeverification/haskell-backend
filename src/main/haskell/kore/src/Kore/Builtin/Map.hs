{- |
Module      : Kore.Builtin.Map
Description : Built-in key-value maps
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
    , Builtin
    , asPattern
    , asExpandedPattern
      -- * Symbols
    , lookupSymbolUnit
    , lookupSymbolUpdate
    , lookupSymbolLookup
    , lookupSymbolElement
    , lookupSymbolConcat
    , lookupSymbolInKeys
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
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
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
    , ( "MAP.in_keys"
      , Builtin.verifySymbol Bool.assertSort [anySort, assertSort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

type Builtin = Map (Kore.CommonPurePattern Object) (Kore.CommonPurePattern Object)

{- | Abort function evaluation if the argument is not a Map domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinDomainMap
    :: Monad m
    => String  -- ^ Context for error message
    -> Kore.CommonPurePattern Object  -- ^ Operand pattern
    -> ExceptT (AttemptedFunction Object Kore.Variable) m Builtin
expectBuiltinDomainMap ctx =
    \case
        Kore.DV_ _ domain ->
            case domain of
                Kore.BuiltinDomainMap map' -> return map'
                _ -> Builtin.verifierBug (ctx ++ ": Domain value is not a map")
        _ ->
            Except.throwError NotApplicable

getAttemptedFunction :: Monad m => ExceptT r m r -> m r
getAttemptedFunction = fmap (either id id) . runExceptT

returnMap
    :: Monad m
    => Kore.Sort Object
    -> Builtin
    -> m (AttemptedFunction Object Kore.Variable)
returnMap resultSort map' =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ Kore.DV_ resultSort
        $ Kore.BuiltinDomainMap map'

evalLookup :: Builtin.Function
evalLookup =
    Builtin.functionEvaluator evalLookup0
  where
    evalLookup0 _ _ _ arguments =
        getAttemptedFunction
        (do
            let (_map, key) =
                    case arguments of
                        [_map, key'] -> (_map, key')
                        _ -> Builtin.wrongArity "MAP.lookup"
            _map <- expectBuiltinDomainMap "MAP.lookup" _map
            Builtin.appliedFunction
                $ maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern
                $ Map.lookup key _map
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
            let (_map, key, value) =
                    case arguments of
                        [_map, key', value'] -> (_map, key', value')
                        _ -> Builtin.wrongArity "MAP.update"
            _map <- expectBuiltinDomainMap "MAP.update" _map
            returnMap resultSort (Map.insert key value _map)
        )

evalInKeys :: Builtin.Function
evalInKeys =
    Builtin.functionEvaluator evalInKeys0
  where
    evalInKeys0 _ _ resultSort = \arguments ->
        getAttemptedFunction
        (do
            let (key, _map) =
                    case arguments of
                        [key', _map] -> (key', _map)
                        _ -> Builtin.wrongArity "MAP.in_keys"
            _map <- expectBuiltinDomainMap "MAP.in_keys" _map
            Builtin.appliedFunction
                $ Bool.asExpandedPattern resultSort
                $ Map.member key _map
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
        , ("MAP.in_keys", evalInKeys)
        ]

{- | Render a 'Map' as a domain value pattern of the given sort.

    The result sort should be hooked to the builtin @Map@ sort, but this is not
    checked.

    The constructed pattern will be valid in the contexed of the given indexed
    module. It is an error if the indexed module does not define symbols hooked
    to @MAP.unit@, @MAP.element@, and @MAP.concat@.

    See also: 'sort'

 -}
asPattern
    :: KoreIndexedModule attrs
    -- ^ indexed module where pattern would appear
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin -> Kore.CommonPurePattern Object)
asPattern indexedModule _
  = do
    symbolUnit <- lookupSymbolUnit indexedModule
    let applyUnit = Kore.App_ symbolUnit []
    symbolElement <- lookupSymbolElement indexedModule
    let applyElement (k, v) = Kore.App_ symbolElement [k, v]
    symbolConcat <- lookupSymbolConcat indexedModule
    let applyConcat map1 map2 = Kore.App_ symbolConcat [map1, map2]
        asPattern0 result =
            foldr applyConcat applyUnit
                (applyElement <$> Map.toAscList result)
    return asPattern0

{- | Render a 'Map' as an extended domain value pattern.

    See also: 'asPattern'

 -}
asExpandedPattern
    :: KoreIndexedModule attrs
    -- ^ dictionary of Map constructor symbols
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin -> CommonExpandedPattern Object)
asExpandedPattern symbols resultSort =
    (ExpandedPattern.fromPurePattern .) <$> asPattern symbols resultSort

{- | Find the symbol hooked to @MAP.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "MAP.unit"

{- | Find the symbol hooked to @MAP.update@ in an indexed module.
 -}
lookupSymbolUpdate
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUpdate = Builtin.lookupSymbol "MAP.update"

{- | Find the symbol hooked to @MAP.lookup@ in an indexed module.
 -}
lookupSymbolLookup
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolLookup = Builtin.lookupSymbol "MAP.lookup"

{- | Find the symbol hooked to @MAP.element@ in an indexed module.
 -}
lookupSymbolElement
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "MAP.element"

{- | Find the symbol hooked to @MAP.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "MAP.concat"

{- | Find the symbol hooked to @MAP.in_keys@ in an indexed module.
 -}
lookupSymbolInKeys
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolInKeys = Builtin.lookupSymbol "MAP.in_keys"
