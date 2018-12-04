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
    , lookupSymbolKeys
    , isSymbolConcat
    -- * Unification
    , unifyEquals
    -- * Raw evaluators
    , evalConcat
    , evalElement
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Pure as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 SimplificationType, Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Step.Substitution
                 ( normalize )
import           Kore.Variables.Fresh

{- | Builtin name of the @Map@ sort.
 -}
sort :: Text
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
    , ( "MAP.keys"
      , Builtin.verifySymbol Builtin.Set.assertSort [assertSort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

type Builtin variable =
    Map (ConcreteStepPattern Object) (StepPattern Object variable)

{- | Abort function evaluation if the argument is not a Map domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinMap
    :: Monad m
    => String  -- ^ Context for error message
    -> StepPattern Object variable  -- ^ Operand pattern
    -> MaybeT m (Builtin variable)
expectBuiltinMap ctx _map =
    do
        case _map of
            DV_ _ domain ->
                case domain of
                    Domain.BuiltinMap map' -> return map'
                    _ ->
                        Builtin.verifierBug
                            (ctx ++ ": Domain value is not a map")
            _ ->
                empty

returnMap
    :: (Monad m, Ord (variable Object))
    => Sort Object
    -> Builtin variable
    -> m (AttemptedFunction Object variable)
returnMap resultSort map' =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ asBuiltinDomainValue resultSort map'

evalLookup :: Builtin.Function
evalLookup =
    Builtin.functionEvaluator evalLookup0
  where
    ctx = "MAP.lookup"
    evalLookup0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalLookup0 tools _ _ arguments =
        Builtin.getAttemptedFunction
        (do
            let (_map, _key) =
                    case arguments of
                        [_map, _key] -> (_map, _key)
                        _ -> Builtin.wrongArity ctx
                emptyMap = do
                    _map <- expectBuiltinMap ctx _map
                    if Map.null _map
                        then Builtin.appliedFunction ExpandedPattern.bottom
                        else empty
                bothConcrete = do
                    _key <- Builtin.expectNormalConcreteTerm tools _key
                    _map <- expectBuiltinMap ctx _map
                    Builtin.appliedFunction $ maybeBottom $ Map.lookup _key _map
            emptyMap <|> bothConcrete
        )
    maybeBottom = maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern

-- | evaluates the map element builtin.
evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_key, _value) =
                    case arguments of
                        [_key, _value] -> (_key, _value)
                        _ -> Builtin.wrongArity "MAP.element"
            _key <- Builtin.expectNormalConcreteTerm tools _key
            returnMap resultSort (Map.singleton _key _value)
        )

-- | evaluates the map concat builtin.
evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    ctx = "MAP.concat"
    evalConcat0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalConcat0 _ _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_map1, _map2) =
                    case arguments of
                        [_map1, _map2] -> (_map1, _map2)
                        _ -> Builtin.wrongArity ctx
                leftIdentity = do
                    _map1 <- expectBuiltinMap ctx _map1
                    if Map.null _map1
                        then
                            Builtin.appliedFunction
                            $ ExpandedPattern.fromPurePattern _map2
                        else
                            empty
                rightIdentity = do
                    _map2 <- expectBuiltinMap ctx _map2
                    if Map.null _map2
                        then
                            Builtin.appliedFunction
                            $ ExpandedPattern.fromPurePattern _map1
                        else
                            empty
                bothConcrete = do
                    _map1 <- expectBuiltinMap ctx _map1
                    _map2 <- expectBuiltinMap ctx _map2
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
                            Builtin.appliedFunction ExpandedPattern.bottom
                        else
                            returnMap resultSort (Map.union _map1 _map2)
            leftIdentity <|> rightIdentity <|> bothConcrete
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
    evalUpdate0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_map, _key, value) =
                    case arguments of
                        [_map, _key, value'] -> (_map, _key, value')
                        _ -> Builtin.wrongArity "MAP.update"
            _key <- Builtin.expectNormalConcreteTerm tools _key
            _map <- expectBuiltinMap "MAP.update" _map
            returnMap resultSort (Map.insert _key value _map)
        )

evalInKeys :: Builtin.Function
evalInKeys =
    Builtin.functionEvaluator evalInKeys0
  where
    evalInKeys0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_key, _map) =
                    case arguments of
                        [_key, _map] -> (_key, _map)
                        _ -> Builtin.wrongArity "MAP.in_keys"
            _key <- Builtin.expectNormalConcreteTerm tools _key
            _map <- expectBuiltinMap "MAP.in_keys" _map
            Builtin.appliedFunction
                $ Bool.asExpandedPattern resultSort
                $ Map.member _key _map
        )

evalKeys :: Builtin.Function
evalKeys =
    Builtin.functionEvaluator evalKeys0
  where
    ctx = "MAP.in_keys"
    evalKeys0
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object variable
        -> Sort Object
        -> [StepPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalKeys0 _ _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let _map =
                    case arguments of
                        [_map] -> _map
                        _ -> Builtin.wrongArity ctx
            _map <- expectBuiltinMap ctx _map
            Builtin.Set.returnSet resultSort (Map.keysSet _map)
        )

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ ("MAP.concat", evalConcat)
        , ("MAP.lookup", evalLookup)
        , ("MAP.element", evalElement)
        , ("MAP.unit", evalUnit)
        , ("MAP.update", evalUpdate)
        , ("MAP.in_keys", evalInKeys)
        , ("MAP.keys", evalKeys)
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
    -> Sort Object
    -> Either
        (Kore.Error e)
        (Builtin variable -> StepPattern Object variable)
asPattern indexedModule dvSort
  = do
    symbolUnit <- lookupSymbolUnit dvSort indexedModule
    let applyUnit = App_ symbolUnit []
    symbolElement <- lookupSymbolElement dvSort indexedModule
    let applyElement (key, value) =
            App_ symbolElement [Kore.fromConcretePurePattern key, value]
    symbolConcat <- lookupSymbolConcat dvSort indexedModule
    let applyConcat map1 map2 = App_ symbolConcat [map1, map2]
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
    -> Either
        (Kore.Error e)
        (Builtin variable -> ExpandedPattern Object variable)
asExpandedPattern symbols resultSort =
    asExpandedPattern0 <$> asPattern symbols resultSort
  where
    asExpandedPattern0 = \asPattern0 builtin ->
        ExpandedPattern.fromPurePattern $ asPattern0 builtin

{- | Embed a 'Map' in a builtin domain value pattern.
 -}
asBuiltinDomainValue
    :: Sort Object
    -> Builtin variable
    -> StepPattern Object variable
asBuiltinDomainValue resultSort map' = DV_ resultSort (Domain.BuiltinMap map')

{- | Find the symbol hooked to @MAP.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "MAP.unit"

{- | Find the symbol hooked to @MAP.update@ in an indexed module.
 -}
lookupSymbolUpdate
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolUpdate = Builtin.lookupSymbol "MAP.update"

{- | Find the symbol hooked to @MAP.lookup@ in an indexed module.
 -}
lookupSymbolLookup
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolLookup = Builtin.lookupSymbol "MAP.lookup"

{- | Find the symbol hooked to @MAP.element@ in an indexed module.
 -}
lookupSymbolElement
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "MAP.element"

{- | Find the symbol hooked to @MAP.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "MAP.concat"

{- | Find the symbol hooked to @MAP.in_keys@ in an indexed module.
 -}
lookupSymbolInKeys
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolInKeys = Builtin.lookupSymbol "MAP.in_keys"

{- | Find the symbol hooked to @MAP.keys@ in an indexed module.
 -}
lookupSymbolKeys
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (SymbolOrAlias Object)
lookupSymbolKeys = Builtin.lookupSymbol "MAP.keys"

{- | Check if the given symbol is hooked to @MAP.concat@.
 -}
isSymbolConcat
    :: MetadataTools Object Hook
    -> SymbolOrAlias Object
    -> Bool
isSymbolConcat = Builtin.isSymbol "MAP.concat"

{- | Check if the given symbol is hooked to @MAP.element@.
 -}
isSymbolElement
    :: MetadataTools Object Hook
    -> SymbolOrAlias Object
    -> Bool
isSymbolElement = Builtin.isSymbol "MAP.element"

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
    :: forall level variable m p expanded proof .
        ( OrdMetaOrObject variable, ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        , MetaOrObject level
        , FreshVariable variable
        , Show (variable level)
        , p ~ StepPattern level variable
        , expanded ~ ExpandedPattern level variable
        , proof ~ SimplificationProof level
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> (p -> p -> m (expanded, proof))
    -> (p -> p -> MaybeT m (expanded, proof))
unifyEquals
    simplificationType
    tools@MetadataTools { symbolOrAliasSorts }
    substitutionSimplifier
    unifyEqualsChildren
  =
    unifyEquals0
  where
    hookTools = StepperAttributes.hook <$> tools

    -- | Discard the proofs in a collection of proven expanded patterns.
    discardProofs :: Map k (expanded, proof) -> Map k expanded
    discardProofs = Map.map fst

    -- | Given a collection 't' of 'Predicated' values, propagate all the
    -- predicates to the top level, returning a 'Predicated' collection.
    propagatePredicates
        :: (level ~ Object, Traversable t)
        => t (Predicated level variable a)
        -> Predicated level variable (t a)
    propagatePredicates = give symbolOrAliasSorts sequenceA

    -- | Unify the two argument patterns.
    unifyEquals0
        :: StepPattern level variable
        -> StepPattern level variable
        -> MaybeT m (expanded, proof)

    unifyEquals0 dv1@(DV_ resultSort (Domain.BuiltinMap map1)) =
        \case
            dv2@(DV_ _ builtin2) ->
                case builtin2 of
                    Domain.BuiltinMap map2 ->
                        Monad.Trans.lift
                        $ unifyEqualsConcrete resultSort map1 map2
                    _ ->
                        (error . unlines)
                            [ "Cannot unify a builtin Map domain value:"
                            , show dv1
                            , "with:"
                            , show dv2
                            , "This should have been a sort error."
                            ]
            app@(App_ symbol2 args2)
                | isSymbolConcat hookTools symbol2 ->
                    -- Accept the arguments of MAP.concat in either order.
                    Monad.Trans.lift $ case args2 of
                        [ DV_ _ (Domain.BuiltinMap map2), x@(Var_ _) ] ->
                            unifyEqualsFramed1 resultSort dv1 map2 x
                        [ x@(Var_ _), DV_ _ (Domain.BuiltinMap map2) ] ->
                            unifyEqualsFramed1 resultSort dv1 map2 x
                        [ _, _ ] ->
                            give symbolOrAliasSorts
                                (Builtin.unifyEqualsUnsolved
                                    simplificationType dv1 app
                                )
                        _ ->
                            Builtin.wrongArity "MAP.concat"
                | isSymbolElement hookTools symbol2 ->
                    Monad.Trans.lift $ case args2 of
                        [ key2, value2 ] ->
                            -- The key is not concrete yet, or MAP.element would
                            -- have evaluated to a domain value.
                            unifyEqualsElement map1 symbol2 key2 value2
                        _ ->
                            Builtin.wrongArity "MAP.element"
                | otherwise ->
                    empty
            _ ->
                empty

    unifyEquals0 pat1 =
        \case
            dv@(DV_ _ (Domain.BuiltinMap _)) -> unifyEquals0 dv pat1
            _ -> empty

    -- | Unify two concrete maps.
    unifyEqualsConcrete
        ::  forall k.
            (level ~ Object, k ~ ConcreteStepPattern Object)
        => Sort level  -- ^ result sort
        -> Map k (StepPattern level variable)
        -> Map k (StepPattern level variable)
        -> m (expanded, proof)
    unifyEqualsConcrete resultSort map1 map2 = do
        intersect <-
            sequence (Map.intersectionWith unifyEqualsChildren map1 map2)
        let
            result
              | not (Map.null remainder1) =
                -- There is nothing with which to unify the
                -- remainder of map1.
                ExpandedPattern.bottom
              | not (Map.null remainder2) =
                -- There is nothing with which to unify the
                -- remainder of map2.
                ExpandedPattern.bottom
              | otherwise =
                asBuiltinMap <$> (propagatePredicates . discardProofs) intersect
              where
                -- Elements of map1 missing from map2
                remainder1 = Map.difference map1 map2
                -- Elements of map2 missing from map1
                remainder2 = Map.difference map2 map1

        return (result, SimplificationProof)
      where
        asBuiltinMap = asBuiltinDomainValue resultSort

    -- | Unify one concrete map with one framed concrete map.
    unifyEqualsFramed1
        :: forall k . (level ~ Object, k ~ ConcreteStepPattern Object)
        => Sort level  -- ^ Sort of result
        -> p  -- ^ concrete map
        -> Map k p  -- ^ framed concrete map
        -> p  -- ^ framing variable
        -> m (expanded, proof)
    unifyEqualsFramed1
        resultSort
        dv1@(DV_ _ (Domain.BuiltinMap map1))
        map2
        x
      = do
        intersect <-
            sequence (Map.intersectionWith unifyEqualsChildren map1 map2)
        -- The framing variable unifies with the remainder of map1.
        let remainder1 = Map.difference map1 map2
        -- The framing part of the unification result.
        (frame, _) <- unifyEqualsChildren x (asBuiltinMap remainder1)
        let
            -- The concrete part of the unification result.
            concrete :: ExpandedPattern level variable
            concrete =
                asBuiltinMap <$> (propagatePredicates . discardProofs) intersect

            result
              | not (Map.null remainder2) =
                -- There is nothing with which to unify the remainder of map2.
                ExpandedPattern.bottom
              | otherwise = give symbolOrAliasSorts $
                    pure dv1 -- (DV_ resultSort (BuiltinDomainMap map1))
                    <* concrete
                    <* frame
              where
                -- Elements of map2 missing from map1
                remainder2 = Map.difference map2 map1

        normalized <- normalize tools substitutionSimplifier result
        return (normalized, SimplificationProof)
      where
        asBuiltinMap = asBuiltinDomainValue resultSort

    unifyEqualsFramed1 _ _ _ _ = error "The impossible happened"


    unifyEqualsElement
        :: forall k . (level ~ Object, k ~ ConcreteStepPattern Object)
        => Map k p  -- ^ concrete map
        -> SymbolOrAlias level  -- ^ 'element' symbol
        -> p  -- ^ key
        -> p  -- ^ value
        -> m (expanded, proof)
    unifyEqualsElement map1 element' key2 value2 =
        case Map.toList map1 of
            [(Kore.fromConcretePurePattern -> key1, value1)] ->
                give symbolOrAliasSorts $ do
                    (key, _) <- unifyEqualsChildren key1 key2
                    (value, _) <- unifyEqualsChildren value1 value2
                    let result =
                            App_ element' <$> args
                          where
                            args = propagatePredicates [key, value]
                    return (result, SimplificationProof)
            _ ->
                -- Cannot unify a non-element Map with an element Map.
                return (ExpandedPattern.bottom, SimplificationProof)
