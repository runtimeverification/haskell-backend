{- |
Module      : Kore.Builtin.List
Description : Built-in associative lists
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.List as List
@
 -}
module Kore.Builtin.List
    ( sort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    , Builtin
    , asPattern
    , asExpandedPattern
      -- * Symbols
    , lookupSymbolUnit
    , lookupSymbolElement
    , lookupSymbolConcat
    , lookupSymbolGet
    ) where

import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import qualified Control.Monad.Except as Except
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )


{- | Builtin name of the @List@ sort.
 -}
sort :: String
sort = "LIST.List"

{- | Verify that the sort is hooked to the builtin @List@ sort.

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
    [ ( "LIST.concat"
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( "LIST.element"
      , Builtin.verifySymbol assertSort [anySort]
      )
    , ( "LIST.unit"
      , Builtin.verifySymbol assertSort []
      )
    , ( "LIST.get"
      , Builtin.verifySymbol anySort [assertSort, Int.assertSort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

type Builtin = Seq (CommonPurePattern Object)

{- | Abort function evaluation if the argument is not a List domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainList', it is a bug.

 -}
expectBuiltinDomainList
    :: Monad m
    => String  -- ^ Context for error message
    -> CommonPurePattern Object  -- ^ Operand pattern
    -> ExceptT (AttemptedFunction Object Kore.Variable) m Builtin
expectBuiltinDomainList ctx =
    \case
        Kore.DV_ _ domain ->
            case domain of
                Kore.BuiltinDomainList list -> return list
                _ -> Builtin.verifierBug (ctx ++ ": Domain value is not a list")
        _ ->
            Except.throwError NotApplicable

getAttemptedFunction :: Monad m => ExceptT r m r -> m r
getAttemptedFunction = fmap (either id id) . runExceptT

returnList
    :: Monad m
    => Kore.Sort Object
    -> Builtin
    -> m (AttemptedFunction Object Kore.Variable)
returnList resultSort list =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ Kore.DV_ resultSort
        $ Kore.BuiltinDomainList list

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ _ resultSort = \arguments ->
        case arguments of
            [elem'] -> returnList resultSort (Seq.singleton elem')
            _ -> Builtin.wrongArity "LIST.element"

evalGet :: Builtin.Function
evalGet =
    Builtin.functionEvaluator evalGet0
  where
    evalGet0 _ _ _ = \arguments ->
        getAttemptedFunction
        (do
            let (_list, _ix) =
                    case arguments of
                        [_list, _ix] -> (_list, _ix)
                        _ -> Builtin.wrongArity "LIST.get"
            _list <- expectBuiltinDomainList "LIST.get" _list
            _ix <- fromInteger <$> Int.expectBuiltinDomainInt "LIST.get" _ix
            let ix | _ix < 0 =
                     -- negative indices count from end of list
                     _ix + Seq.length _list
                   | otherwise = _ix
            (Builtin.appliedFunction . fromMaybe) (Seq.lookup ix _list)
        )
    fromMaybe =
        maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ _ resultSort =
        \case
            [] -> returnList resultSort Seq.empty
            _ -> Builtin.wrongArity "LIST.unit"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0 _ _ resultSort = \arguments ->
        getAttemptedFunction
        (do
            let (_list1, _list2) =
                    case arguments of
                        [_list1, _list2] -> (_list1, _list2)
                        _ -> Builtin.wrongArity "LIST.concat"
            _list1 <- expectBuiltinDomainList "LIST.concat" _list1
            _list2 <- expectBuiltinDomainList "LIST.concat" _list2
            returnList resultSort (_list1 <> _list2)
        )

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
        [ ("LIST.concat", evalConcat)
        , ("LIST.element", evalElement)
        , ("LIST.unit", evalUnit)
        , ("LIST.get", evalGet)
        ]

{- | Render a 'Seq' as a domain value pattern of the given sort.

    The result sort should be hooked to the builtin @List@ sort, but this is not
    checked.

    The constructed pattern will be valid in the contexed of the given indexed
    module. It is an error if the indexed module does not define symbols hooked
    to @LIST.unit@, @LIST.element@, and @LIST.concat@.

    See also: 'sort'

 -}
asPattern
    :: KoreIndexedModule attrs
    -- ^ indexed module where pattern would appear
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin -> CommonPurePattern Object)
asPattern indexedModule _ = do
    symbolUnit <- lookupSymbolUnit indexedModule
    let applyUnit = Kore.App_ symbolUnit []
    symbolElement <- lookupSymbolElement indexedModule
    let applyElement elem' = Kore.App_ symbolElement [elem']
    symbolConcat <- lookupSymbolConcat indexedModule
    let applyConcat list1 list2 = Kore.App_ symbolConcat [list1, list2]
    let asPattern0 list =
            foldr applyConcat applyUnit
            $ Foldable.toList (applyElement <$> list)
    return asPattern0

{- | Render a 'Seq' as an extended domain value pattern.

    See also: 'asPattern'

 -}
asExpandedPattern
    :: KoreIndexedModule attrs
    -- ^ dictionary of Map constructor symbols
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin -> CommonExpandedPattern Object)
asExpandedPattern symbols resultSort =
    (ExpandedPattern.fromPurePattern .) <$> asPattern symbols resultSort

{- | Find the symbol hooked to @LIST.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "LIST.unit"

{- | Find the symbol hooked to @LIST.element@ in an indexed module.
 -}
lookupSymbolElement
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "LIST.element"

{- | Find the symbol hooked to @LIST.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "LIST.concat"

{- | Find the symbol hooked to @LIST.get@ in an indexed module.
 -}
lookupSymbolGet
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolGet = Builtin.lookupSymbol "LIST.get"
