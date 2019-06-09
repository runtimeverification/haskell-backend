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
    , asInternal
    , asTermLike
      -- * Symbols
    , lookupSymbolUpdate
    , lookupSymbolLookup
    , lookupSymbolInKeys
    , lookupSymbolKeys
    , lookupSymbolRemove
    , lookupSymbolRemoveAll
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , isSymbolRemove
    , isSymbolRemoveAll
      -- * keys
    , concatKey
    , lookupKey
    , elementKey
    , unitKey
    , updateKey
    , in_keysKey
    , keysKey
    -- * Unification
    , unifyEquals
    -- * Raw evaluators
    , evalConcat
    , evalElement
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT, fromMaybe )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Reflection as Reflection
import qualified Data.Set as Set
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Bool
import           Kore.Builtin.Builtin
                 ( acceptAnySort )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SmtMetadataTools )
import           Kore.Internal.Conditional
                 ( Conditional, andCondition )
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Predicate )
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.Syntax.Sentence
                 ( SentenceSort (..) )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparseToString )
import           Kore.Variables.Fresh

{- | Builtin name of the @Map@ sort.
 -}
sort :: Text
sort = "MAP.Map"

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers =
    HashMap.fromList [ (sort, verifySortDecl) ]
  where
    verifySortDecl indexedModule sentenceSort attrs = do
        Builtin.verifySortDecl indexedModule sentenceSort attrs
        unitId <- Builtin.getUnitId attrs
        Builtin.assertSymbolHook indexedModule unitId unitKey
        Builtin.assertSymbolResultSort indexedModule unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook indexedModule elementId elementKey
        Builtin.assertSymbolResultSort indexedModule elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook indexedModule concatId concatKey
        Builtin.assertSymbolResultSort indexedModule concatId expectedSort
        return ()
      where
        SentenceSort { sentenceSortName } = sentenceSort
        expectedSort = mkSort sentenceSortName

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( concatKey
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( elementKey
      , Builtin.verifySymbol assertSort [acceptAnySort, acceptAnySort]
      )
    , ( lookupKey
      , Builtin.verifySymbol acceptAnySort [assertSort, acceptAnySort]
      )
    , ( unitKey
      , Builtin.verifySymbol assertSort []
      )
    , ( updateKey
      , Builtin.verifySymbol assertSort
            [assertSort, acceptAnySort, acceptAnySort]
      )
    , ( in_keysKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
      )
    , ( keysKey
      , Builtin.verifySymbol Builtin.Set.assertSort [assertSort]
      )
    , ( removeKey
      , Builtin.verifySymbol assertSort [assertSort, acceptAnySort]
      )
    , ( removeAllKey
      , Builtin.verifySymbol assertSort [assertSort, Builtin.Set.assertSort]
      )
    ]

{- | Abort function evaluation if the argument is not a Map domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinMap
    :: Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Map (TermLike Concrete) (TermLike variable))
expectBuiltinMap ctx (Builtin_ builtin) =
    case builtin of
        Domain.BuiltinMap Domain.InternalMap { builtinMapChild } ->
            return builtinMapChild
        _ ->
            Builtin.verifierBug
            $ Text.unpack ctx ++ ": Domain value is not a map"
expectBuiltinMap _ _ = empty

returnMap
    :: (MonadSimplify m, Ord variable)
    => Sort
    -> Map (TermLike Concrete) (TermLike variable)
    -> m (AttemptedAxiom variable)
returnMap resultSort map' = do
    tools <- Simplifier.askMetadataTools
    Builtin.appliedFunction
        $ Pattern.fromTermLike
        $ asInternal tools resultSort map'

evalLookup :: Builtin.Function
evalLookup =
    Builtin.functionEvaluator evalLookup0
  where
    evalLookup0 :: Builtin.FunctionImplementation
    evalLookup0 _ _ arguments =
        Builtin.getAttemptedAxiom $ do
            let (_map, _key) =
                    case arguments of
                        [_map, _key] -> (_map, _key)
                        _ -> Builtin.wrongArity lookupKey
                emptyMap = do
                    _map <- expectBuiltinMap lookupKey _map
                    if Map.null _map
                        then Builtin.appliedFunction Pattern.bottom
                        else empty
                bothConcrete = do
                    _key <- Builtin.expectNormalConcreteTerm _key
                    _map <- expectBuiltinMap lookupKey _map
                    Builtin.appliedFunction $ maybeBottom $ Map.lookup _key _map
            emptyMap <|> bothConcrete
      where
        maybeBottom = maybe Pattern.bottom Pattern.fromTermLike

-- | evaluates the map element builtin.
evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_key, _value) =
                    case arguments of
                        [_key, _value] -> (_key, _value)
                        _ -> Builtin.wrongArity elementKey
            _key <- Builtin.expectNormalConcreteTerm _key
            returnMap resultSort (Map.singleton _key _value)

-- | evaluates the map concat builtin.
evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_map1, _map2) =
                    case arguments of
                        [_map1, _map2] -> (_map1, _map2)
                        _ -> Builtin.wrongArity concatKey
                leftIdentity = do
                    _map1 <- expectBuiltinMap concatKey _map1
                    if Map.null _map1
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _map2
                        else
                            empty
                rightIdentity = do
                    _map2 <- expectBuiltinMap concatKey _map2
                    if Map.null _map2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _map1
                        else
                            empty
                bothConcrete = do
                    _map1 <- expectBuiltinMap concatKey _map1
                    _map2 <- expectBuiltinMap concatKey _map2
                    let overlapping =
                            (not . Set.null)
                                (Set.intersection
                                    (Map.keysSet _map1)
                                    (Map.keysSet _map2)
                                )
                    if overlapping
                        then
                            -- Result is ‘\bottom{}()’ when there is overlap
                            -- between the keys of the operands.
                            Builtin.appliedFunction Pattern.bottom
                        else
                            returnMap resultSort (Map.union _map1 _map2)
            leftIdentity <|> rightIdentity <|> bothConcrete

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ resultSort =
        \case
            [] -> returnMap resultSort Map.empty
            _ -> Builtin.wrongArity unitKey

evalUpdate :: Builtin.Function
evalUpdate =
    Builtin.functionEvaluator evalUpdate0
  where
    evalUpdate0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_map, _key, value) =
                    case arguments of
                        [_map, _key, value'] -> (_map, _key, value')
                        _ -> Builtin.wrongArity updateKey
            _key <- Builtin.expectNormalConcreteTerm _key
            _map <- expectBuiltinMap updateKey _map
            returnMap resultSort (Map.insert _key value _map)

evalInKeys :: Builtin.Function
evalInKeys =
    Builtin.functionEvaluator evalInKeys0
  where
    evalInKeys0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_key, _map) =
                    case arguments of
                        [_key, _map] -> (_key, _map)
                        _ -> Builtin.wrongArity in_keysKey
            _key <- Builtin.expectNormalConcreteTerm _key
            _map <- expectBuiltinMap in_keysKey _map
            Builtin.appliedFunction
                $ Bool.asPattern resultSort
                $ Map.member _key _map

evalKeys :: Builtin.Function
evalKeys =
    Builtin.functionEvaluator evalKeys0
  where
    evalKeys0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let _map =
                    case arguments of
                        [_map] -> _map
                        _ -> Builtin.wrongArity lookupKey
            _map <- expectBuiltinMap lookupKey _map
            Builtin.Set.returnSet resultSort (Map.keysSet _map)

evalRemove :: Builtin.Function
evalRemove =
    Builtin.functionEvaluator evalRemove0
  where
    evalRemove0 :: Builtin.FunctionImplementation
    evalRemove0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_map, _key) =
                    case arguments of
                        [_map, _key] -> (_map, _key)
                        _ -> Builtin.wrongArity removeKey
                emptyMap = do
                    _map <- expectBuiltinMap removeKey _map
                    if Map.null _map
                        then returnMap resultSort Map.empty
                        else empty
                bothConcrete = do
                    _map <- expectBuiltinMap removeKey _map
                    _key <- Builtin.expectNormalConcreteTerm _key
                    returnMap resultSort $ Map.delete _key _map
            emptyMap <|> bothConcrete

evalRemoveAll :: Builtin.Function
evalRemoveAll =
    Builtin.functionEvaluator evalRemoveAll0
  where
    evalRemoveAll0 :: Builtin.FunctionImplementation
    evalRemoveAll0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_map, _set) =
                    case arguments of
                        [_map, _set] -> (_map, _set)
                        _ -> Builtin.wrongArity removeAllKey
                emptyMap = do
                    _map <- expectBuiltinMap removeAllKey _map
                    if Map.null _map
                        then returnMap resultSort Map.empty
                        else empty
                bothConcrete = do
                    _map <- expectBuiltinMap removeAllKey _map
                    _set <- Builtin.Set.expectBuiltinSet removeAllKey _set
                    returnMap resultSort $ Map.withoutKeys _map _set
            emptyMap <|> bothConcrete


{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (concatKey, evalConcat)
        , (lookupKey, evalLookup)
        , (elementKey, evalElement)
        , (unitKey, evalUnit)
        , (updateKey, evalUpdate)
        , (in_keysKey, evalInKeys)
        , (keysKey, evalKeys)
        , (removeKey, evalRemove)
        , (removeAllKey, evalRemoveAll)
        ]

{- | Render a 'Map' as an internal pattern of the given sort.

The result sort must be hooked to the builtin @Map@ sort.

See also: 'sort'

 -}
asInternal
    :: Ord variable
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Map (TermLike Concrete) (TermLike variable)
    -> TermLike variable
asInternal tools builtinMapSort builtinMapChild =
    (mkBuiltin . Domain.BuiltinMap)
        Domain.InternalMap
            { builtinMapSort
            , builtinMapUnit =
                Builtin.lookupSymbolUnit builtinMapSort attrs
            , builtinMapElement =
                Builtin.lookupSymbolElement builtinMapSort attrs
            , builtinMapConcat =
                Builtin.lookupSymbolConcat builtinMapSort attrs
            , builtinMapChild
            }
  where
    attrs = sortAttributes tools builtinMapSort

{- | Render an 'Domain.InternalMap' as a 'TermLike' domain value pattern.
 -}
asTermLike
    :: Ord variable
    => Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable
asTermLike builtin
  | Map.null map' = unit
  | otherwise = foldr1 concat' (element <$> Map.toAscList map')
  where
    Domain.InternalMap { builtinMapSort = builtinSort } = builtin
    Domain.InternalMap { builtinMapChild = map' } = builtin
    Domain.InternalMap { builtinMapUnit = unitSymbol } = builtin
    Domain.InternalMap { builtinMapElement = elementSymbol } = builtin
    Domain.InternalMap { builtinMapConcat = concatSymbol } = builtin

    apply = mkApplySymbol builtinSort
    unit = apply unitSymbol []
    element (key, value) = apply elementSymbol [fromConcrete key, value]
    concat' map1 map2 = apply concatSymbol [map1, map2]

{- | Render a 'Map' a domain value 'Pattern'.

See also: 'asPattern'

 -}
asPattern
    ::  ( Ord variable
        , Given (SmtMetadataTools Attribute.Symbol)
        )
    => Sort
    -> Map (TermLike Concrete) (TermLike variable)
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal tools resultSort
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = Reflection.given

concatKey :: IsString s => s
concatKey = "MAP.concat"

lookupKey :: IsString s => s
lookupKey = "MAP.lookup"

elementKey :: IsString s => s
elementKey = "MAP.element"

unitKey :: IsString s => s
unitKey = "MAP.unit"

updateKey :: IsString s => s
updateKey = "MAP.update"

in_keysKey :: IsString s => s
in_keysKey = "MAP.in_keys"

keysKey :: IsString s => s
keysKey = "MAP.keys"

removeKey :: IsString s => s
removeKey = "MAP.remove"

removeAllKey :: IsString s => s
removeAllKey = "MAP.removeAll"

{- | Find the symbol hooked to @MAP.update@ in an indexed module.
 -}
lookupSymbolUpdate
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolUpdate = Builtin.lookupSymbol updateKey

{- | Find the symbol hooked to @MAP.lookup@ in an indexed module.
 -}
lookupSymbolLookup
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolLookup = Builtin.lookupSymbol lookupKey

{- | Find the symbol hooked to @MAP.in_keys@ in an indexed module.
 -}
lookupSymbolInKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolInKeys = Builtin.lookupSymbol in_keysKey

{- | Find the symbol hooked to @MAP.keys@ in an indexed module.
 -}
lookupSymbolKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolKeys = Builtin.lookupSymbol keysKey

{- | Find the symbol hooked to @MAP.remove@ in an indexed module.
 -}
lookupSymbolRemove
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolRemove = Builtin.lookupSymbol removeKey

{- | Find the symbol hooked to @MAP.removeAll@ in an indexed module.
 -}
lookupSymbolRemoveAll
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolRemoveAll = Builtin.lookupSymbol removeAllKey

{- | Check if the given symbol is hooked to @MAP.concat@.
 -}
isSymbolConcat
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @MAP.element@.
 -}
isSymbolElement
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @MAP.unit@.
-}
isSymbolUnit
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

{- | Check if the given symbol is hooked to @MAP.remove@.
-}
isSymbolRemove
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolRemove = Builtin.isSymbol removeKey

{- | Check if the given symbol is hooked to @MAP.removeAll@.
-}
isSymbolRemoveAll
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolRemoveAll = Builtin.isSymbol removeAllKey

{- | Simplify the conjunction or equality of two concrete Map domain values.

When it is used for simplifying equality, one should separately solve the
case ⊥ = ⊥. One should also throw away the term in the returned pattern.

The maps are assumed to have the same sort, but this is not checked. If
multiple sorts are hooked to the same builtin domain, the verifier should
reject the definition.

The most general form of the unification problem is
@
(m₁ + x₁) ∧ (m₂ + x₂)
@
where @+@ represents @concat@ and @m₁@, @m₂@ are concrete maps.
The solution is to introduce @qᵢ@ and @rᵢ@ such that
@
m₁ = q₁ + r₁
m₂ = q₂ + r₂
keys(q₁) = keys(q₂)
keys(r₁) ∧ keys(r₂) = ⊥
@
so that
@
(m₁ + x₁) ∧ (m₂ + x₂) = (q₁ ∧ q₂) + (r₁ + x₁) ∧ (r₂ + x₂).
@
When both @x₁@ and @x₂@ are present, we should check that @q₁ ∧ q₂@ is not
empty, otherwise this equation is just a trivial shuffling and does not actually
make progress toward simplification. We introduce special cases when @x₁@ and/or
@x₂@ is missing.
 -}
-- TODO (thomas.tuegel): Handle the case of two framed maps.
unifyEquals
    ::  forall variable unifier
    .   ( SortedVariable variable
        , FreshVariable variable
        , Show variable
        , Unparse variable
        , MonadUnify unifier
        )
    => SimplificationType
    -> SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyEquals
    simplificationType
    tools
    _
    _
    _
    unifyEqualsChildren
    first
    second
  =
    unifyEquals0 first second
  where
    hookTools = Attribute.hook <$> tools

    -- | Given a collection 't' of 'Conditional' values, propagate all the
    -- predicates to the top, returning a 'Conditional' collection.
    propagatePredicates
        :: Traversable t
        => t (Conditional variable a)
        -> Conditional variable (t a)
    propagatePredicates = sequenceA

    -- | Unify the two argument patterns.
    unifyEquals0
        :: TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)

    unifyEquals0
        dv1@(Builtin_ (Domain.BuiltinMap builtin1))
        dv2@(Builtin_ internal2)
      =
        case internal2 of
            Domain.BuiltinMap builtin2 ->
                Monad.Trans.lift $ unifyEqualsConcrete builtin1 builtin2
            _ ->
                (error . unlines)
                    [ "Cannot unify a builtin Map domain value:"
                    , show dv1
                    , "with:"
                    , show dv2
                    , "This should have been a sort error."
                    ]

    unifyEquals0
        dv1@(Builtin_ (Domain.BuiltinMap builtin1))
        app2@(App_ symbol2 args2)
      | isSymbolConcat hookTools symbol2 =
        -- Accept the arguments of MAP.concat in either order.
        Monad.Trans.lift $ case args2 of
            [ Builtin_ (Domain.BuiltinMap builtin2), x@(Var_ _) ] ->
                unifyEqualsFramed1 builtin1 builtin2 x
            [ x@(Var_ _), Builtin_ (Domain.BuiltinMap builtin2) ] ->
                unifyEqualsFramed1 builtin1 builtin2 x
            [ App_ symbol3 [ key3, value3 ], x ]
                | isSymbolElement hookTools symbol3 ->
                unifyEqualsSelect builtin1 symbol3 key3 value3 x
            [ x, App_ symbol3 [ key3, value3 ] ]
                | isSymbolElement hookTools symbol3 ->
                unifyEqualsSelect builtin1 symbol3 key3 value3 x
            [ _, _ ] ->
                Builtin.unifyEqualsUnsolved
                    simplificationType
                    dv1
                    app2
            _ ->
                Builtin.wrongArity "MAP.concat"
      | isSymbolElement hookTools symbol2 =
        Monad.Trans.lift $ case args2 of
            [ key2, value2 ] ->
                -- The key is not concrete yet, or MAP.element would
                -- have evaluated to a domain value.
                unifyEqualsElement
                    builtin1
                    key2
                    value2
            _ ->
                Builtin.wrongArity "MAP.element"
      | isSymbolUnit hookTools symbol2 =
        Monad.Trans.lift $ case args2 of
            [] -> unifyEqualsUnit builtin1
            _ -> Builtin.wrongArity "MAP.unit"
      | otherwise =
        (error . unlines)
            [ "Unimplemented map unification for domain value vs application. "
            , "dv=" ++ unparseToString dv1
            , "app=" ++ unparseToString app2
            ]
          where
        -- Unify one concrete map with a select pattern (k:key v:value s:map)
        -- Note that k and v can be a proper symbolic patterns
        -- (not just variables).
        -- TODO(virgil): move it from where once the otherwise is not needed
        unifyEqualsSelect
            ::  Domain.InternalMap
                    (TermLike Concrete)
                    (TermLike variable)  -- ^ concrete map
            -> Symbol                    -- ^ 'element' symbol
            -> TermLike variable         -- ^ key
            -> TermLike variable         -- ^ value
            -> TermLike variable         -- ^ remainder for unification
            -> unifier (Pattern variable)
        unifyEqualsSelect builtin1' _ key2 value2 map2
          | map1 == Map.empty = bottomWithExplanation
          | otherwise =
            Reflection.give tools $ do
                (concreteKey1, value1) <- Monad.Unify.scatter (Map.toList map1)
                let remainderMap = Map.delete concreteKey1 map1
                    remainderMapPat = asInternal tools sort1 remainderMap
                    key1 = fromConcrete concreteKey1

                keyUnifier <- unifyEqualsChildren key1 key2
                valueUnifier <- unifyEqualsChildren value1 value2

                mapUnifier <- unifyEqualsChildren remainderMapPat map2

                let
                    mapUnifierTerm :: TermLike variable
                    mapUnifierPredicate :: Predicate variable
                    (mapUnifierTerm, mapUnifierPredicate) =
                        Pattern.splitTerm mapUnifier
                    mapUnifierMap :: Map (TermLike Concrete) (TermLike variable)
                    mapUnifierMap = case mapUnifierTerm of
                        (Builtin_
                            (Domain.BuiltinMap
                                Domain.InternalMap { builtinMapChild }
                            )
                         ) -> builtinMapChild
                        _ -> (error . unlines)
                            [ "Unexpected map unification term."
                            , "builtin=" ++ unparseToString builtin1
                            , "key2=" ++ unparseToString key2
                            , "unifier=" ++ unparseToString mapUnifier
                            ]

                    eitherResult =
                        addKeyValuePatternsToMap
                            tools sort1 keyUnifier valueUnifier mapUnifierMap
                case eitherResult of
                    Left KeyInMap -> do
                        Monad.Unify.explainBottom
                            "After unification the key was found in the map."
                            first
                            second
                        empty
                    Right result ->
                        return (result `andCondition` mapUnifierPredicate)

          | otherwise =
            Builtin.unifyEqualsUnsolved simplificationType dv1 app2
          where
            Domain.InternalMap
                { builtinMapChild = map1
                , builtinMapSort = sort1
                } = builtin1'

    unifyEquals0 (Builtin_ (Domain.BuiltinMap _)) _ = empty

    unifyEquals0 pat1 dv@(Builtin_ (Domain.BuiltinMap _)) =
        unifyEquals0 dv pat1

    unifyEquals0 _ _ = empty

    -- | Unify two concrete maps.
    unifyEqualsConcrete
        :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -> Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -> unifier (Pattern variable)
    unifyEqualsConcrete builtin1 builtin2 = do
        intersect <-
            sequence (Map.intersectionWith unifyEqualsChildren map1 map2)
        let
            result
              | not (Map.null remainder1) =
                -- There is nothing with which to unify the
                -- remainder of map1.
                bottomWithExplanation
              | not (Map.null remainder2) = bottomWithExplanation
              | otherwise =
                return $ asInternal tools builtinMapSort
                    <$> propagatePredicates intersect
              where
                -- Elements of map1 missing from map2
                remainder1 = Map.difference map1 map2
                -- Elements of map2 missing from map1
                remainder2 = Map.difference map2 map1

        result
      where
        Domain.InternalMap { builtinMapSort } = builtin1
        Domain.InternalMap { builtinMapChild = map1 } = builtin1
        Domain.InternalMap { builtinMapChild = map2 } = builtin2

    -- | Unify one concrete map with one framed concrete map.
    unifyEqualsFramed1
        :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -- ^ concrete map
        -> Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -- ^ framed map
        -> TermLike variable  -- ^ framing variable
        -> unifier (Pattern variable)
    unifyEqualsFramed1 builtin1 builtin2 x = do
        intersect <-
            sequence (Map.intersectionWith unifyEqualsChildren map1 map2)
        -- The framing variable unifies with the remainder of map1.
        let remainder1 = Map.difference map1 map2
        -- The framing part of the unification result.
        frame <- unifyEqualsChildren x (asBuiltinMap remainder1)
        let
            -- The concrete part of the unification result.
            concrete :: Pattern variable
            concrete = asBuiltinMap <$> propagatePredicates intersect

            result
              | not (Map.null remainder2) = bottomWithExplanation
              | otherwise =
                return $
                    Reflection.give tools asPattern builtinMapSort map1
                    <* concrete
                    <* frame
              where
                -- Elements of map2 missing from map1
                remainder2 = Map.difference map2 map1

        result
      where
        Domain.InternalMap { builtinMapSort } = builtin1
        Domain.InternalMap { builtinMapChild = map1 } = builtin1
        Domain.InternalMap { builtinMapChild = map2 } = builtin2
        asBuiltinMap = asInternal tools builtinMapSort

    unifyEqualsElement
        :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -- ^ concrete map
        -> TermLike variable  -- ^ key
        -> TermLike variable  -- ^ value
        -> unifier (Pattern variable)
    unifyEqualsElement builtin1 key2 value2 =
        case Map.toList map1 of
            [(fromConcrete -> key1, value1)] -> do
                keyUnifier <- unifyEqualsChildren key1 key2
                valueUnifier <- unifyEqualsChildren value1 value2

                let
                    eitherResult =
                        addKeyValuePatternsToMap
                            tools sort1 keyUnifier valueUnifier Map.empty
                case eitherResult of
                    Left KeyInMap -> (error . unlines)
                        [ "Unexpected key in empty map."
                        , "key=" ++ unparseToString keyUnifier
                        , "value=" ++ unparseToString valueUnifier
                        ]
                    Right result -> return result
            _ -> bottomWithExplanation
            -- Cannot unify a non-element Map with an element Map
      where
        Domain.InternalMap { builtinMapSort = sort1 } = builtin1
        Domain.InternalMap { builtinMapChild = map1 } = builtin1

    unifyEqualsUnit
        :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
        -- ^ concrete map
        -> unifier (Pattern variable)
    unifyEqualsUnit builtin1 =
        if null map1
            then return
                (Pattern.fromTermLike
                    (mkBuiltin $ Domain.BuiltinMap builtin1)
                )
            else bottomWithExplanation
            -- Cannot unify a non-element Map with an element Map
      where
        Domain.InternalMap { builtinMapChild = map1 } = builtin1

    bottomWithExplanation :: unifier (Pattern variable)
    bottomWithExplanation = do
        Monad.Unify.explainBottom
            "Cannot unify a non-element map with an element map."
            first
            second
        empty

data KeyInMap = KeyInMap

addKeyValuePatternsToMap
    :: forall variable
    .   ( Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Pattern variable
    -> Pattern variable
    -> Map (TermLike Concrete) (TermLike variable)
    -> Either KeyInMap (Pattern variable)
addKeyValuePatternsToMap tools sort1 keyPattern valuePattern existingMap =
    if Map.member concreteKeyTerm existingMap
    then Left KeyInMap
    else Right
        (pure (asInternal tools sort1 newMap)
            `andCondition` keyPredicate
            `andCondition` valuePredicate
        )
  where
    keyTerm :: TermLike variable
    keyPredicate :: Predicate variable
    (keyTerm, keyPredicate) = Pattern.splitTerm keyPattern
    concreteKeyTerm :: TermLike Concrete
    concreteKeyTerm =
        fromMaybe
            ((error . unlines)
                [ "Unexpected variable in map key term"
                , "key=" ++ unparseToString keyPattern
                ]
            )
            (asConcrete keyTerm)

    valueTerm :: TermLike variable
    valuePredicate :: Predicate variable
    (valueTerm, valuePredicate) = Pattern.splitTerm valuePattern

    newMap :: Map (TermLike Concrete) (TermLike variable)
    newMap = Map.insert concreteKeyTerm valueTerm existingMap
