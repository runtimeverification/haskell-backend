{- |
Module      : Kore.Builtin.AssociativeCommutative
Description : Handles built-in operations which are associative, commutative,
              with neutral elements, key-based, with unique keys, and which
              return bottom when applied to unique keys.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.AssociativeCommutative as Ac
@
-}

module Kore.Builtin.AssociativeCommutative
    ( asInternal
    , asInternalConcrete
    , asPattern
    , asTermLike
    , ConcatSymbol(..)
    , ConcreteElements (..)
    , evalConcatNormalizedOrBottom
    , NormalizedOrBottom (..)
    , Opaque (..)
    , returnAc
    , returnConcreteAc
    , TermWrapper (..)
    , TermNormalizedAc
    , unifyEqualsNormalized
    , UnitSymbol(..)
    , VariableElements (..)
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT, partitionEithers )
import qualified Control.Lens as Lens
import           Control.Monad
                 ( foldM, unless )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.List
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Reflection as Reflection
import           Data.Text.Prettyprint.Doc
                 ( Doc )
import           GHC.Stack
                 ( HasCallStack )

import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.MapSymbols as Map
import qualified Kore.Builtin.SetSymbols as Set
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Conditional
                 ( Conditional, andCondition, withCondition )
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.Symbol
                 ( Symbol )
import           Kore.Internal.TermLike
                 ( pattern App_, pattern Builtin_, Concrete, TermLike,
                 pattern Var_, mkApplySymbol, mkBuiltin, termLikeSort )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Sort
                 ( Sort )
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.Step.Simplification.Data
                 ( AttemptedAxiom, emptyAttemptedAxiom )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse, unparseToString )
import qualified Kore.Unparser as Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Class for things that can fill the @builtinAcChild@ value of a
@InternalAc@ struct inside a @Domain.Builtin.Builtin@ value.

There is a bijection between @normalized@ and @valueWrapper@ types
(see @Domain.AcWrapper@).
-}
class
    ( Domain.AcWrapper (normalized :: * -> * -> *)
    , valueWrapper ~ Domain.Value normalized
    )
    -- TODO (thomas.tuegel): Remove second parameter
    => TermWrapper normalized valueWrapper
  where
    {- | Render a normalized value (e.g. 'NormalizedSet') as a Domain.Builtin.

    The result sort must be hooked to the builtin normalized sort (e.g. @Set@).
    -}
    asInternalBuiltin
        :: SmtMetadataTools Attribute.Symbol
        -> Sort
        -> normalized key child
        -> Domain.Builtin key child
    {- |Transforms a @TermLike@ representation into a @NormalizedOrBottom@.

    The term may become bottom if we had conflicts between elements that were
    not detected before, e.g.

    @
    concat({1}, concat(X:Set, {1}))
    concat(elem(Y:Int), concat({1}, elem(Y:Int)))
    concat(X:Set, concat({1}, X:Set))
    @
    -}
    toNormalized
        :: Ord variable
        => SmtMetadataTools Attribute.Symbol
        -> TermLike variable
        -> NormalizedOrBottom normalized variable

instance TermWrapper Domain.NormalizedMap Domain.MapValue where
    {- | Render a 'NormalizedMap' as a Domain.Builtin.

    The result sort must be hooked to the builtin @Map@ sort.
    -}
    asInternalBuiltin tools builtinAcSort builtinAcChild =
        Domain.BuiltinMap Domain.InternalAc
            { builtinAcSort
            , builtinAcUnit = Builtin.lookupSymbolUnit tools builtinAcSort
            , builtinAcElement = Builtin.lookupSymbolElement tools builtinAcSort
            , builtinAcConcat = Builtin.lookupSymbolConcat tools builtinAcSort
            , builtinAcChild
            }
    {- |Transforms a @TermLike@ representation into a @NormalizedOrBottom@.

    The map may become bottom if we had conflicts between elements that were
    not detected before, e.g.

    @
    concat({1->"a"}, concat(X:Map, {1}))
    concat(elem(Y:Int), concat({1}, elem(Y:Int)))
    concat(X:Map, concat({1}, X:Map))
    @
    -}
    toNormalized
        _tools
        (Builtin_ (Domain.BuiltinMap Domain.InternalAc { builtinAcChild }))
      = Normalized (Domain.unwrapAc builtinAcChild)
    toNormalized tools (App_ symbol args)
      | Map.isSymbolUnit hookTools symbol =
        case args of
            [] -> Normalized Domain.emptyNormalizedAc
            _ -> Builtin.wrongArity "MAP.unit"
      | Map.isSymbolElement hookTools symbol =
        case args of
            [key, value] ->
                Normalized Domain.NormalizedAc
                    { elementsWithVariables = [Domain.MapElement (key, value)]
                    , concreteElements = Map.empty
                    , opaque = []
                    }
            _ -> Builtin.wrongArity "MAP.element"
      | Map.isSymbolConcat hookTools symbol =
        case args of
            [set1, set2] ->
                toNormalized tools set1 <> toNormalized tools set2
            _ -> Builtin.wrongArity "MAP.concat"
      where
        hookTools = Attribute.Symbol.hook <$> tools
    toNormalized _ patt =
        Normalized Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = Map.empty
            , opaque = [patt]
            }

instance TermWrapper Domain.NormalizedSet Domain.SetValue where
    {- | Render a 'NormalizedSet' as a Domain.Builtin.

    The result sort must be hooked to the builtin @Set@ sort.
    -}
    asInternalBuiltin tools builtinAcSort builtinAcChild =
        Domain.BuiltinSet Domain.InternalAc
            { builtinAcSort
            , builtinAcUnit = Builtin.lookupSymbolUnit tools builtinAcSort
            , builtinAcElement = Builtin.lookupSymbolElement tools builtinAcSort
            , builtinAcConcat = Builtin.lookupSymbolConcat tools builtinAcSort
            , builtinAcChild
            }
    {- |Transforms a @TermLike@ representation into a @NormalizedSetOrBottom@.

    The set may become bottom if we had conflicts between elements that were
    not detected before, e.g.

    @
    concat({1}, concat(X:Set, {1}))
    concat(elem(Y:Int), concat({1}, elem(Y:Int)))
    concat(X:Set, concat({1}, X:Set))
    @
    -}
    toNormalized
        _tools
        (Builtin_ (Domain.BuiltinSet Domain.InternalAc { builtinAcChild }))
      = Normalized (Domain.unwrapAc builtinAcChild)
    toNormalized tools (App_ symbol args)
      | Set.isSymbolUnit hookTools symbol =
        case args of
            [] -> Normalized Domain.emptyNormalizedAc
            _ -> Builtin.wrongArity "SET.unit"
      | Set.isSymbolElement hookTools symbol =
        case args of
            [elem1] ->
                Normalized Domain.NormalizedAc
                    { elementsWithVariables = [Domain.SetElement elem1]
                    , concreteElements = Map.empty
                    , opaque = []
                    }
            _ -> Builtin.wrongArity "SET.element"
      | Set.isSymbolConcat hookTools symbol =
        case args of
            [set1, set2] ->
                toNormalized tools set1 <> toNormalized tools set2
            _ -> Builtin.wrongArity "SET.concat"
      where
        hookTools = Attribute.Symbol.hook <$> tools
    toNormalized _ patt =
        Normalized Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = Map.empty
            , opaque = [patt]
            }

{- | Wrapper for terms that keeps the "concrete" vs "with variable" distinction
after converting @TermLike Concrete@ to @TermLike variable@.
-}
data ConcreteOrWithVariable valueWrapper variable
    = ConcretePat (TermLike variable, valueWrapper (TermLike variable))
    | WithVariablePat (TermLike variable, valueWrapper (TermLike variable))

fromConcreteOrWithVariable
    :: ConcreteOrWithVariable valueWrapper variable
    -> (TermLike variable, valueWrapper (TermLike variable))
fromConcreteOrWithVariable (ConcretePat result) = result
fromConcreteOrWithVariable (WithVariablePat result) = result

{- | Particularizes @Domain.NormalizedAc@ to the most common types.
-}
type TermNormalizedAc collection variable =
    Domain.NormalizedAc collection (TermLike Concrete) (TermLike variable)

{-| A normalized representation of an associative-commutative structure that
also allows bottom values.
-}
data NormalizedOrBottom collection variable
    = Normalized (TermNormalizedAc collection variable)
    | Bottom

deriving instance
    ( Eq variable
    , Eq (Domain.Element collection (TermLike variable))
    , Eq (Domain.Value collection (TermLike variable))
    ) =>
    Eq (NormalizedOrBottom collection variable)

deriving instance
    ( Show variable
    , Show (Domain.Element collection (TermLike variable))
    , Show (Domain.Value collection (TermLike variable))
    ) =>
    Show (NormalizedOrBottom collection variable)

{- | The semigroup defined by the `concat` operation.
-}
instance
    (Ord variable, Domain.AcWrapper collection) =>
    Semigroup (NormalizedOrBottom collection variable)
  where
    Bottom <> _ = Bottom
    _ <> Bottom = Bottom
    Normalized Domain.NormalizedAc
        { elementsWithVariables =
            map Domain.unwrapElement -> elementsWithVariables1
        , concreteElements = concreteElements1
        , opaque = opaque1
        }
      <> Normalized Domain.NormalizedAc
        { elementsWithVariables =
            map Domain.unwrapElement -> elementsWithVariables2
        , concreteElements = concreteElements2
        , opaque = opaque2
        }
      = case mergeDisjoint of
        Nothing -> Bottom
        Just result -> Normalized result
      where
        mergeDisjoint = do
            withVariables <-
                addAllListDisjoint elementsWithVariables1 elementsWithVariables2
            concrete <- addAllMapDisjoint concreteElements1 concreteElements2
            -- We may have common opaque terms if they are empty, so we can't
            -- do an `addAll*Disjoint` as above.
            let allOpaque = Data.List.sort (opaque1 ++ opaque2)
            return Domain.NormalizedAc
                { elementsWithVariables =
                    Lens.review Domain.elementIso <$> withVariables
                , concreteElements = concrete
                , opaque = allOpaque
                }
        addAllMapDisjoint map1 map2 = addToMapDisjoint map1 (Map.toList map2)
        addAllListDisjoint :: Ord a => [(a, b)] -> [(a, b)] -> Maybe [(a, b)]
        addAllListDisjoint map1 = addToListDisjoint (Map.fromList map1) map1

{- | The monoid defined by the `concat` and `unit` operations.
-}
instance
    (Ord variable, Domain.AcWrapper collection) =>
    Monoid (NormalizedOrBottom collection variable)
  where
    mempty = Normalized Domain.emptyNormalizedAc

{- | Computes the union of two maps if they are disjoint. Returns @Nothing@
otherwise.
-}
addToMapDisjoint
    :: (Ord a, Traversable t) => Map a b -> t (a, b) -> Maybe (Map a b)
addToMapDisjoint existing traversable = do
    (_, mapResult) <- foldM addElementDisjoint ([], existing) traversable
    return mapResult

{- | Computes the union of two ac structures if they are disjoint.
Returns @Nothing@ otherwise.
-}
addToListDisjoint
    :: (Ord a, Traversable t)
    => Map a b
    -> [(a, b)]
    -> t (a, b)
    -> Maybe [(a, b)]
addToListDisjoint map1 list1 list2 = do
    (listResult, _) <- foldM addElementDisjoint (list1, map1) list2
    return listResult

addElementDisjoint
    :: Ord a
    => ([(a, b)], Map a b) -> (a, b) -> Maybe ([(a, b)], Map a b)
addElementDisjoint (list, existing) (key, value) =
    if key `Map.member` existing
    then Nothing
    else return ((key, value) : list, Map.insert key value existing)

{- | Given a @NormalizedAc@, returns it as a function result.
-}
returnAc
    ::  ( MonadSimplify m
        , Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        )
    => Sort
    -> TermNormalizedAc normalized variable
    -> m (AttemptedAxiom variable)
returnAc resultSort ac = do
    tools <- Simplifier.askMetadataTools
    Builtin.appliedFunction
        $ Pattern.fromTermLike
        $ asInternal tools resultSort ac

{- | Converts an Ac of concrete elements to a @NormalizedAc@ and returns it
as a function result.
-}
returnConcreteAc
    ::  ( MonadSimplify m
        , Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        )
    => Sort
    -> Map (TermLike Concrete) (valueWrapper (TermLike variable))
    -> m (AttemptedAxiom variable)
returnConcreteAc resultSort concrete =
    returnAc
        resultSort
        Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = concrete
            , opaque = []
            }

{- | Render an Ac structure as an internal domain value pattern of the given
sort.

The result sort must be hooked to the right builtin sort. The pattern will use
the internal representation of the domain values; it will not use a
valid external representation. Use 'asPattern' to construct an externally-valid
pattern.

-}
asInternal
    ::  ( Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> TermNormalizedAc normalized variable
    -> TermLike variable
asInternal tools builtinAcSort builtinAcChild =
    mkBuiltin
        (asInternalBuiltin tools builtinAcSort (Domain.wrapAc builtinAcChild))

{- | The same as 'asInternal', but for ac structures made only of concrete
elements.
-}
asInternalConcrete
    ::  ( Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Map (TermLike Concrete) (valueWrapper (TermLike variable))
    -> TermLike variable
asInternalConcrete tools sort1 concreteAc =
    asInternal
        tools
        sort1
        Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = concreteAc
            , opaque = []
            }

elementListAsInternal
    :: forall normalized valueWrapper variable
    .   ( Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> [(TermLike variable, valueWrapper (TermLike variable))]
    -> Maybe (TermLike variable)
elementListAsInternal tools sort1 terms = do
    let (withVariables, concrete) = splitVariableConcrete terms
    _checkDisjoinVariables <- disjointMap withVariables
    concreteAc <- disjointMap concrete
    return
        (asInternal
            tools
            sort1
            Domain.NormalizedAc
                { elementsWithVariables =
                    Lens.review Domain.elementIso <$> withVariables
                , concreteElements = concreteAc
                , opaque = []
                }
        )

{- | Render a 'NormalizedAc' as an extended domain value pattern.
-}
asPattern
    ::  ( Ord variable, SortedVariable variable
        , Given (SmtMetadataTools Attribute.Symbol)
        , TermWrapper normalized valueWrapper
        )
    => Sort
    -> TermNormalizedAc normalized variable
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal tools resultSort
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = Reflection.given

{- | Evaluates a concatenation of two AC structures represented as
NormalizedOrBottom, providind the result in the form of a function result.
-}
evalConcatNormalizedOrBottom
    :: forall m normalized valueWrapper variable
    .   ( MonadSimplify m
        , Ord variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        )
    => Sort
    -> NormalizedOrBottom normalized variable
    -> NormalizedOrBottom normalized variable
    -> MaybeT m (AttemptedAxiom variable)
evalConcatNormalizedOrBottom _ Bottom _ = return emptyAttemptedAxiom
evalConcatNormalizedOrBottom _ _ Bottom = return emptyAttemptedAxiom
evalConcatNormalizedOrBottom
    resultSort
    (Normalized normalized1)
    (Normalized normalized2)
  =
    case concatNormalized normalized1 normalized2 of
        Nothing -> return emptyAttemptedAxiom
        Just concatenation -> returnAc resultSort concatenation
  where
    concatNormalized
        :: forall child key
        .  (Ord key, Ord child)
        => Domain.NormalizedAc normalized key child
        -> Domain.NormalizedAc normalized key child
        -> Maybe (Domain.NormalizedAc normalized key child)
    -- The NormalizedAc matching is useful only for getting
    -- notified when new fields are being added.
    concatNormalized ac1@(Domain.NormalizedAc _ _ _) ac2 = do
        let
            Domain.NormalizedAc
                { elementsWithVariables =
                    map (Lens.view Domain.elementIso) -> withVariable1
                , concreteElements = concrete1
                , opaque = opaque1
                } = ac1
            Domain.NormalizedAc
                { elementsWithVariables =
                    map (Lens.view Domain.elementIso) -> withVariable2
                , concreteElements = concrete2
                , opaque = opaque2
                } = ac2

        withVariablesPartial <- addToMapDisjoint Map.empty withVariable1
        withVariables <- addToMapDisjoint withVariablesPartial withVariable2

        concrete <- addToMapDisjoint concrete1 (Map.toList concrete2)

        -- If these opaque terms would be non-empty, we could test
        -- for equality as above, but we don't know that.
        let allOpaque = Data.List.sort (opaque1 ++ opaque2)

        return Domain.NormalizedAc
            { elementsWithVariables =
                Lens.review Domain.elementIso <$> Map.toList withVariables
            , concreteElements = concrete
            , opaque = allOpaque
            }


disjointMap :: Ord a => [(a, b)] -> Maybe (Map a b)
disjointMap input =
    if length input == Map.size asMap
    then Just asMap
    else Nothing
  where
    asMap = Map.fromList input

splitVariableConcrete
    :: [(TermLike variable, a)]
    -> ([(TermLike variable, a)], [(TermLike Concrete, a)])
splitVariableConcrete terms =
    partitionEithers (map toConcreteEither terms)
  where
    toConcreteEither
        :: (TermLike variable, a)
        -> Either (TermLike variable, a) (TermLike Concrete, a)
    toConcreteEither (term, a) =
        case TermLike.asConcrete term of
            Nothing -> Left (term, a)
            Just result -> Right (result, a)

{- | Simplify the conjunction or equality of two Ac domain values in their
normalized form.

When it is used for simplifying equality, one should separately solve the
case ⊥ = ⊥. One should also throw away the term in the returned pattern.

The domain values are assumed to have the same sort, but this is not checked. If
multiple sorts are hooked to the same builtin domain, the verifier should
reject the definition.
-}
unifyEqualsNormalized
    :: forall normalized unifier (valueWrapper :: * -> *) variable
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , Traversable valueWrapper
        , FreshVariable variable
        , TermWrapper normalized valueWrapper
        , MonadUnify unifier
        , Unparse (valueWrapper (TermLike variable))
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> Domain.InternalAc (TermLike Concrete) normalized (TermLike variable)
    -> Domain.InternalAc (TermLike Concrete) normalized (TermLike variable)
    -> MaybeT unifier (Pattern variable)
unifyEqualsNormalized
    tools
    first
    second
    unifyEqualsChildren
    normalized1
    normalized2
  = do
    let
        Domain.InternalAc { builtinAcChild = firstWrapped } =
            normalized1
        Domain.InternalAc { builtinAcChild = secondWrapped } =
            normalized2
        firstNormalized = Domain.unwrapAc firstWrapped
        secondNormalized = Domain.unwrapAc secondWrapped

    unifierNormalized <-
        unifyEqualsNormalizedAc
            tools
            first
            second
            unifyEqualsChildren
            firstNormalized
            secondNormalized
    let
        unifierNormalizedTerm :: TermNormalizedAc normalized variable
        unifierPredicate :: Predicate variable
        (unifierNormalizedTerm, unifierPredicate) =
            Conditional.splitTerm unifierNormalized
        normalizedTerm :: TermLike variable
        normalizedTerm = asInternal tools sort1 unifierNormalizedTerm

    -- TODO(virgil): Check whether this normalization is still needed
    -- (the normalizedTerm may already be re-normalized) and remove it if not.
    renormalized <- normalize1 normalizedTerm

    let unifierTerm :: TermLike variable
        unifierTerm = asInternal tools sort1 renormalized
    return (unifierTerm `withCondition` unifierPredicate)
  where
    sort1 = termLikeSort first

    normalize1
        ::  ( MonadUnify unifier
            , Ord variable
            )
        => TermLike variable
        -> MaybeT unifier (TermNormalizedAc normalized variable)
    normalize1 patt =
        case toNormalized tools patt of
            Bottom -> Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                "Duplicated elements in normalization."
                first
                second
            Normalized n -> return n

{- | Unifies two AC structs represented as @NormalizedAc@.

Currently allows at most one opaque term in the two arguments taken together.
-}
unifyEqualsNormalizedAc
    ::  forall normalized valueWrapper variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , Traversable valueWrapper
        , FreshVariable variable
        , TermWrapper normalized valueWrapper
        , MonadUnify unifier
        , Unparse (valueWrapper (TermLike variable))
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermNormalizedAc normalized variable
    -> TermNormalizedAc normalized variable
    -> MaybeT
        unifier
        (Conditional variable (TermNormalizedAc normalized variable))
unifyEqualsNormalizedAc
    tools
    first
    second
    unifyEqualsChildren
    Domain.NormalizedAc
        { elementsWithVariables =
            map (Lens.view Domain.elementIso) -> elementsWithVariables1
        , concreteElements = concreteElements1
        , opaque = opaque1
        }
    Domain.NormalizedAc
        { elementsWithVariables =
            map (Lens.view Domain.elementIso) -> elementsWithVariables2
        , concreteElements = concreteElements2
        , opaque = opaque2
        }
  = do
    (simpleUnifier, opaques) <- case (opaqueDifference1, opaqueDifference2) of
        ([], []) -> Monad.Trans.lift $
            unifyEqualsElementLists'
                allElements1
                allElements2
                Nothing
        ([opaque], []) ->
            Monad.Trans.lift $
                unifyEqualsElementLists'
                    allElements1
                    allElements2
                    (Just opaque)
        ([], [opaque]) ->
            Monad.Trans.lift $
                unifyEqualsElementLists'
                    allElements2
                    allElements1
                    (Just opaque)
        (_, _) -> empty
    let (unifiedElements, unifierPredicate) =
            Conditional.splitTerm simpleUnifier
    Monad.Trans.lift $ do -- unifier monad
        -- unify the parts not sent to unifyEqualsNormalizedElements.
        (commonElementsTerms, commonElementsPredicate) <-
            unifyElementList (Map.toList commonElements)
        (commonVariablesTerms, commonVariablesPredicate) <-
            unifyElementList (Map.toList commonVariables)

        -- simplify results so that things like inj applications that
        -- may have been broken into smaller pieces are being put
        -- back together.
        unifiedSimplified <- mapM simplifyPair unifiedElements
        opaquesSimplified <- mapM simplify opaques

        buildResultFromUnifiers
            tools
            bottomWithExplanation
            commonElementsTerms
            commonVariablesTerms
            commonOpaque
            unifiedSimplified
            opaquesSimplified
            [ unifierPredicate
            , commonElementsPredicate
            , commonVariablesPredicate
            ]
  where
    listToMap :: Ord a => [a] -> Map a Int
    listToMap = List.foldl' (\m k -> Map.insertWith (+) k 1 m) Map.empty
    mapToList :: Map a Int -> [a]
    mapToList =
        Map.foldrWithKey
            (\key count result -> replicate count key ++ result)
            []

    bottomWithExplanation :: Doc () -> unifier a
    bottomWithExplanation explanation =
        Monad.Unify.explainAndReturnBottom explanation first second

    unifyEqualsElementLists' =
        unifyEqualsElementLists
        tools
        first
        second
        unifyEqualsChildren

    opaque1Map = listToMap opaque1
    opaque2Map = listToMap opaque2

    elementsWithVariables1Map = Map.fromList elementsWithVariables1
    elementsWithVariables2Map = Map.fromList elementsWithVariables2

    commonElements =
        Map.intersectionWith
            (,)
            concreteElements1
            concreteElements2
    commonVariables =
        Map.intersectionWith
            (,)
            elementsWithVariables1Map
            elementsWithVariables2Map

    -- Duplicates must be kept in case any of the opaque terms turns out to be
    -- non-empty, in which case one of the terms is bottom, which
    -- means that the unification result is bottom.
    commonOpaqueMap = Map.intersectionWith max opaque1Map opaque2Map

    commonOpaque = mapToList commonOpaqueMap
    commonOpaqueKeys = Map.keysSet commonOpaqueMap

    elementDifference1 =
        Map.toList (Map.difference concreteElements1 commonElements)
    elementDifference2 =
        Map.toList (Map.difference concreteElements2 commonElements)
    elementVariableDifference1 =
        Map.toList (Map.difference elementsWithVariables1Map commonVariables)
    elementVariableDifference2 =
        Map.toList (Map.difference elementsWithVariables2Map commonVariables)
    opaqueDifference1 =
        mapToList (Map.withoutKeys opaque1Map commonOpaqueKeys)
    opaqueDifference2 =
        mapToList (Map.withoutKeys opaque2Map commonOpaqueKeys)

    allElements1 =
        map WithVariablePat elementVariableDifference1
        ++ map toConcretePat elementDifference1
    allElements2 =
        map WithVariablePat elementVariableDifference2
        ++ map toConcretePat elementDifference2

    toConcretePat
        :: (TermLike Concrete, valueWrapper (TermLike variable))
        -> ConcreteOrWithVariable valueWrapper variable
    toConcretePat (a, b) = ConcretePat (TermLike.fromConcrete a, b)

    unifyElementList
        :: forall key
        .   [
                (key
                ,   ( valueWrapper (TermLike variable)
                    , valueWrapper (TermLike variable)
                    )
                )
            ]
        -> unifier
            ( [(key, valueWrapper (TermLike variable))]
            , Predicate variable
            )
    unifyElementList elements = do
        result <-
            mapM
                (unifyCommonElements
                    (\explanation ->
                        Monad.Unify.explainAndReturnBottom
                            explanation first second
                    )
                    unifyEqualsChildren
                )
                elements
        let
            terms :: [(key, valueWrapper (TermLike variable))]
            predicates :: [Predicate variable]
            (terms, predicates) = unzip (map Conditional.splitTerm result)
            predicate :: Predicate variable
            predicate = List.foldl'
                andCondition
                Predicate.top
                predicates

        return (terms, predicate)

    simplify :: TermLike variable -> unifier (Pattern variable)
    simplify term = alternate $ simplifyConditionalTerm term Predicate.top

    simplifyPair
        :: (TermLike variable, valueWrapper (TermLike variable))
        -> unifier
            (Conditional
                variable
                (TermLike variable, valueWrapper (TermLike variable))
            )
    simplifyPair (key, value) = do
        simplifiedKey <- simplifyTermLike key
        let (keyTerm, keyPredicate) = Conditional.splitTerm simplifiedKey
        simplifiedValue <- traverse simplifyTermLike value
        let
            splitSimplifiedValue
                :: valueWrapper (TermLike variable, Predicate variable)
            splitSimplifiedValue =
                fmap Conditional.splitTerm simplifiedValue
            simplifiedValueTerm :: valueWrapper (TermLike variable)
            simplifiedValueTerm = fmap fst splitSimplifiedValue
            simplifiedValuePredicates :: valueWrapper (Predicate variable)
            simplifiedValuePredicates = fmap snd splitSimplifiedValue
            simplifiedValuePredicate :: Predicate variable
            simplifiedValuePredicate =
                foldr
                    andCondition
                    Predicate.top
                    simplifiedValuePredicates
        return
            ((keyTerm, simplifiedValueTerm)
            `withCondition` keyPredicate
            `andCondition` simplifiedValuePredicate
            )
      where
        simplifyTermLike :: TermLike variable -> unifier (Pattern variable)
        simplifyTermLike term =
            alternate $ simplifyConditionalTerm term Predicate.top

buildResultFromUnifiers
    :: forall normalized unifier valueWrapper variable
    .   ( Monad unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> (forall result . Doc () -> unifier result)
    -> [(TermLike Concrete, valueWrapper (TermLike variable))]
    -> [(TermLike variable, valueWrapper (TermLike variable))]
    -> [TermLike variable]
    ->  [ Conditional
            variable
            (TermLike variable, valueWrapper (TermLike variable))
        ]
    -> [Pattern variable]
    -> [Predicate variable]
    -> unifier (Conditional variable (TermNormalizedAc normalized variable))
buildResultFromUnifiers
    tools
    bottomWithExplanation
    commonElementsTerms
    commonVariablesTerms
    commonOpaque
    unifiedElementsSimplified
    opaquesSimplified
    predicates
  = do -- unifier monad
    let
        almostResultTerms
            ::  [(TermLike variable, valueWrapper (TermLike variable))]
        almostResultPredicates :: [Predicate variable]
        (almostResultTerms, almostResultPredicates) =
            unzip (map Conditional.splitTerm unifiedElementsSimplified)
        (withVariableTerms, concreteTerms) =
            splitVariableConcrete almostResultTerms

        (opaquesTerms, opaquesPredicates) =
            unzip (map Conditional.splitTerm opaquesSimplified)
        opaquesNormalized :: NormalizedOrBottom normalized variable
        opaquesNormalized =
            Foldable.fold (map (toNormalized tools) opaquesTerms)

    Domain.NormalizedAc
        { elementsWithVariables =
            map (Lens.view Domain.elementIso) -> opaquesElementsWithVariables
        , concreteElements = opaquesConcreteTerms
        , opaque = opaquesOpaque
        } <- case opaquesNormalized of
            Bottom ->
                bottomWithExplanation "Duplicated elements after unification."
            Normalized result -> return result

    -- Add back all the common objects that were removed before
    -- unification.
    withVariableMap <-
        addAllDisjoint
            bottomWithExplanation
            Map.empty
            (  commonVariablesTerms
            ++ withVariableTerms
            ++ opaquesElementsWithVariables
            )
    concreteMap <-
        addAllDisjoint
            bottomWithExplanation
            Map.empty
            (  commonElementsTerms
            ++ concreteTerms
            ++ Map.toList opaquesConcreteTerms
            )
    let allOpaque = Data.List.sort (commonOpaque ++ opaquesOpaque)
        -- Merge all unification predicates.
        predicate = List.foldl'
            andCondition
            Predicate.top
            (almostResultPredicates ++ opaquesPredicates ++ predicates)
        result
            :: Conditional
                variable
                (Domain.NormalizedAc
                    normalized
                    (TermLike Concrete)
                    (TermLike variable)
                )
        result = Domain.NormalizedAc
            { elementsWithVariables =
                Lens.review Domain.elementIso <$> Map.toList withVariableMap
            , concreteElements = concreteMap
            , opaque = allOpaque
            }
            `Conditional.withCondition` predicate

    return result

addAllDisjoint
    :: (Monad unifier, Ord a)
    => (forall result . Doc () -> unifier result)
    -> Map a b
    -> [(a, b)]
    -> unifier (Map a b)
addAllDisjoint bottomWithExplanation existing elements =
    case addToMapDisjoint existing elements of
        Nothing ->
            bottomWithExplanation "Duplicated elements after AC unification."
        Just result -> return result

unifyCommonElements
    :: forall key normalized unifier variable
    .   ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Traversable (Domain.Value normalized)
        , Unparse variable
        )
    => (forall a . Doc () -> unifier a)
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    ->  ( key
        ,   ( Domain.Value normalized (TermLike variable)
            , Domain.Value normalized (TermLike variable)
            )
        )
    ->  unifier
        ( Conditional variable
            (key, Domain.Value normalized (TermLike variable))
        )
unifyCommonElements
    bottomWithExplanation
    unifier
    (key, (firstValue, secondValue))
  = do
    valuesUnifier <-
        unifyWrappedValues bottomWithExplanation unifier firstValue secondValue
    let
        (valuesTerm, valuePredicate) = Conditional.splitTerm valuesUnifier

    return ((key, valuesTerm) `withCondition` valuePredicate)

unifyWrappedValues
    :: forall normalized unifier variable
    .   ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Traversable (Domain.Value normalized)
        , Unparse variable
        )
    => (forall a . Doc () -> unifier a)
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> Domain.Value normalized (TermLike variable)
    -> Domain.Value normalized (TermLike variable)
    ->  unifier
            (Conditional variable (Domain.Value normalized (TermLike variable)))
unifyWrappedValues bottomWithExplanation unifier firstValue secondValue = do
    zippedValues <- case Domain.acExactZip firstValue secondValue of
        Nothing -> bottomWithExplanation "Unmatched map values"
        Just zipped -> return zipped

    unifiedValues <- traverse (uncurry unifier) zippedValues
    let
        splitValues :: Domain.Value normalized (TermLike variable, Predicate variable)
        splitValues = fmap Pattern.splitTerm unifiedValues
        valueUnifierTerm :: Domain.Value normalized (TermLike variable)
        valueUnifierTerm = fmap fst splitValues
        valuePredicates :: Domain.Value normalized (Predicate variable)
        valuePredicates = fmap snd splitValues
        valueUnifierPredicate :: Predicate variable
        valueUnifierPredicate =
            foldr Conditional.andCondition Predicate.top valuePredicates

    return (valueUnifierTerm `withCondition` valueUnifierPredicate)

{- | Unifies two ac structures given their representation as a list of
@ConcreteOrWithVariable@, with the first structure being allowed an additional
opaque chunk (e.g. a variable) that will be sent to the unifier function
together with some part of the second structure.

The keys of the two structures are assumend to be disjoint.
-}
unifyEqualsElementLists
    ::  forall normalized valueWrapper variable unifier
    .   ( Domain.AcWrapper normalized
        , FreshVariable variable
        , MonadUnify unifier
        , Show variable
        , SortedVariable variable
        , TermWrapper normalized valueWrapper
        , Traversable valueWrapper
        , Unparse (valueWrapper (TermLike variable))
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -- ^ unifier function
    -> [ConcreteOrWithVariable valueWrapper variable]
    -- ^ First structure elements
    -> [ConcreteOrWithVariable valueWrapper variable]
    -- ^ Second structure elements
    -> Maybe (TermLike variable)
    -- ^ Opaque part of the first structure
    -> unifier
        ( Conditional
            variable
            [(TermLike variable, valueWrapper (TermLike variable))]
        , [TermLike variable]
        )
unifyEqualsElementLists
    _tools
    first
    second
    unifyEqualsChildren
    firstElements
    secondElements
    Nothing
  | length firstElements /= length secondElements
    -- Neither the first, not the second ac structure include an opaque term, so
    -- the listed elements form the two structures.
    --
    -- Since the two lists have different counts, their structures can
    -- never unify.
  = Monad.Unify.explainAndReturnBottom
        "Cannot unify ac structures with different sizes."
        first
        second
  | otherwise = do
    (result, remainder1, remainder2) <-
        unifyWithPermutations firstElements secondElements
    -- The second structure does not include an opaque term so there is nothing
    -- to match whatever is left in remainder1. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)
    -- The first structure does not include an opaque term so there is nothing
    -- to match whatever is left in remainder2. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder2)
        (remainderError firstElements secondElements remainder2)

    return (result, [])
  where
    unifyWithPermutations
        :: [ConcreteOrWithVariable valueWrapper variable]
        -- ^ First structure elements
        -> [ConcreteOrWithVariable valueWrapper variable]
        -- ^ Second structure elements
        -> unifier
            (Conditional variable
                [(TermLike variable, valueWrapper (TermLike variable))]
            , [ConcreteOrWithVariable valueWrapper variable]
            , [ConcreteOrWithVariable valueWrapper variable]
            )
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable
                (\explanation ->
                    Monad.Unify.explainAndReturnBottom explanation first second
                )
                unifyEqualsChildren
            )
    remainderError = nonEmptyRemainderError first second
unifyEqualsElementLists
    tools
    first
    second
    unifyEqualsChildren
    firstElements
    secondElements
    (Just opaque)
  | length firstElements > length secondElements
    -- The second structure does not include an opaque term, so all the
    -- elements in the first structure must be matched by elements in the second
    -- one. Since we don't have enough, we return bottom.
  = Monad.Unify.explainAndReturnBottom
        "Cannot unify ac structures with different sizes."
        first
        second
  | otherwise = do
    (unifier, remainder1, remainder2) <-
        unifyWithPermutations firstElements secondElements
    -- The second structure does not include an opaque term so there is nothing
    -- to match whatever is left in remainder1. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)

    let remainder2Terms = map fromConcreteOrWithVariable remainder2

    case elementListAsInternal tools (termLikeSort first) remainder2Terms of
        Nothing -> Monad.Unify.explainAndReturnBottom
            "Duplicated element in unification results"
            first
            second
        Just remainderTerm -> case opaque of
            Var_ _ -> do
                opaqueUnifier <- unifyEqualsChildren opaque remainderTerm
                let
                    (opaqueTerm, opaquePredicate) =
                        Pattern.splitTerm opaqueUnifier
                    result = unifier `andCondition` opaquePredicate

                return (result, [opaqueTerm])
            _ -> (error . unlines)
                [ "Unification case that should be handled somewhere else:"
                , "attempting normalized unification with a non-variable opaque"
                , "term could lead to infinite loops."
                , "first=" ++ unparseToString first
                , "second=" ++ unparseToString second
                ]

  where
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable
                (\explanation ->
                    Monad.Unify.explainAndReturnBottom explanation first second
                )
                unifyEqualsChildren
            )
    remainderError = nonEmptyRemainderError first second

{- |Unifies two patterns represented as @ConcreteOrWithVariable@, making sure
that a concrete pattern (if any) is sent on the first position of the unify
function.

We prefer having a concrete pattern on the first position because the
unifier prefers returning it when it does not know what to use, e.g.

@
unify 10 (f A) ==> 10 and (10 == f A)
unify (f A) 10 ==> (f A) and (10 == f A)
@

and it would probably be more useful to have a concrete term as the
unification term. Also, tests are easier to write.
-}
unifyEqualsConcreteOrWithVariable
    ::  ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Traversable (Domain.Value normalized)
        , Unparse variable
        )
    => (forall a . Doc () -> unifier a)
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> ConcreteOrWithVariable (Domain.Value normalized) variable
    -> ConcreteOrWithVariable (Domain.Value normalized) variable
    -> unifier
        (Conditional
            variable
            (TermLike variable, Domain.Value normalized (TermLike variable))
        )
unifyEqualsConcreteOrWithVariable
    bottomWithExplanation
    unifier
    (ConcretePat concrete1)
    (ConcretePat concrete2)
  = unifyEqualsPair bottomWithExplanation unifier concrete1 concrete2
unifyEqualsConcreteOrWithVariable
    bottomWithExplanation
    unifier
    (ConcretePat concrete1)
    (WithVariablePat withVariable2)
  = unifyEqualsPair bottomWithExplanation unifier concrete1 withVariable2
unifyEqualsConcreteOrWithVariable
    bottomWithExplanation
    unifier
    (WithVariablePat withVariable1)
    (ConcretePat concrete2)
  = unifyEqualsPair bottomWithExplanation unifier concrete2 withVariable1
unifyEqualsConcreteOrWithVariable
    bottomWithExplanation
    unifier
    (WithVariablePat withVariable1)
    (WithVariablePat withVariable2)
  = unifyEqualsPair bottomWithExplanation unifier withVariable1 withVariable2

unifyEqualsPair
    :: forall normalized unifier variable
    .   ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Traversable (Domain.Value normalized)
        , Unparse variable
        )
    => (forall a . Doc () -> unifier a)
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> (TermLike variable, Domain.Value normalized (TermLike variable))
    -> (TermLike variable, Domain.Value normalized (TermLike variable))
    -> unifier
        (Conditional
            variable
            (TermLike variable, Domain.Value normalized (TermLike variable))
        )
unifyEqualsPair
    bottomWithExplanation
    unifier
    (firstKey, firstValue)
    (secondKey, secondValue)
  = do
    keyUnifier <- unifier firstKey secondKey

    valueUnifier <-
        unifyWrappedValues bottomWithExplanation unifier firstValue secondValue

    let
        valueUnifierTerm :: Domain.Value normalized (TermLike variable)
        valueUnifierPredicate :: Predicate variable
        (valueUnifierTerm, valueUnifierPredicate) =
            Conditional.splitTerm valueUnifier

    let (keyUnifierTerm, keyUnifierPredicate) = Pattern.splitTerm keyUnifier

    return
        ((keyUnifierTerm, valueUnifierTerm)
            `withCondition` keyUnifierPredicate
            `andCondition` valueUnifierPredicate
        )


{- | Given a unify function and two lists of unifiable things, returns
all possible ways to unify disjoint pairs of the two that use all items
from at least one of the lists.

Also returns the non-unified part os the lists (one of the two will be empty).
-}
unifyEqualsElementPermutations
    ::  ( Alternative unifier
        , Monad unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => (a -> b -> unifier (Conditional variable c))
    -> [a]
    -> [b]
    -> unifier
        ( Conditional variable [c]
        , [a]
        , [b]
        )
unifyEqualsElementPermutations unifier firsts seconds = do
    (unifiers, remainderFirst, remainderSecond) <-
        if length firsts < length seconds
        then do
            (u, r) <-
                kPermutationsBacktracking (flip unifier) seconds firsts
            return (u, [], r)
        else do
            (u, r) <-
                kPermutationsBacktracking unifier firsts seconds
            return (u, r, [])
    let (terms, predicates) = unzip (map Conditional.splitTerm unifiers)
        predicate = foldr andCondition Predicate.top predicates
    return (terms `withCondition` predicate, remainderFirst, remainderSecond)

{- |Given two lists generates k-permutation pairings and merges them using the
provided merge function.

k is the lenghth of the second list, which means that, if the @[b]@ list is
longer than the @[a]@ list, this will not generate any k-permutations.
However, it will probably take a long time to generate nothing.

If the pairing function fails (i.e. returns empty), the entire function will
stop exploring future branches that would include the given pair.

Note that this does not mean that we won't try a failing pair again with a
different set of previous choices, so this function could be optimized to
at least cache pairing results.
-}
kPermutationsBacktracking
    :: forall a b c m
    .  Alternative m
    => (a -> b -> m c) -> [a] -> [b] -> m ([c], [a])
kPermutationsBacktracking _ first [] = pure ([], first)
kPermutationsBacktracking transform firstList secondList =
    generateKPermutationsWorker firstList [] secondList
  where
    generateKPermutationsWorker :: [a] -> [a] -> [b] -> m ([c], [a])
    generateKPermutationsWorker _ (_:_) [] =
        error "Unexpected non-empty skipped list with empty pair opportunities"
    generateKPermutationsWorker [] [] [] = pure ([], [])
    generateKPermutationsWorker [] _ _ = empty
    generateKPermutationsWorker first [] [] = pure ([], first)
    generateKPermutationsWorker (first : firsts) skipped (second : seconds) =
        pickElement <|> skipElement
      where
        pickElement =
            addToFirst
                <$> transform first second
                <*> generateKPermutationsWorker (skipped ++ firsts) [] seconds

        addToFirst :: x -> ([x], y) -> ([x], y)
        addToFirst x (xs, y) = (x : xs, y)

        skipElement =
            generateKPermutationsWorker
                firsts (first : skipped) (second : seconds)


nonEmptyRemainderError
    :: forall a valueWrapper variable
    .   ( HasCallStack
        , SortedVariable variable
        , Unparse variable
        , Unparse (valueWrapper (TermLike variable))
        )
    => TermLike variable
    -> TermLike variable
    -> [ConcreteOrWithVariable valueWrapper variable]
    -> [ConcreteOrWithVariable valueWrapper variable]
    -> [ConcreteOrWithVariable valueWrapper variable]
    -> a
nonEmptyRemainderError first second input1 input2 remainder =
    (error . unlines)
        [ "Unexpected unused elements, should have been caught"
        , "by checks above:"
        , "first=" ++ unparseToString first
        , "second=" ++ unparseToString second
        , "input1=" ++ unlines (map unparseWrapped input1)
        , "input2=" ++ unlines (map unparseWrapped input2)
        , "remainder=" ++ unlines (map unparseWrapped remainder)
        ]
  where
    unparseWrapped =
        Unparser.renderDefault . unparsePair . fromConcreteOrWithVariable
    unparsePair
        :: (TermLike variable, valueWrapper (TermLike variable)) -> Doc ann
    unparsePair (key, value) = Unparser.arguments' [unparse key, unparse value]

-- | Wrapper for giving names to arguments.
newtype UnitSymbol = UnitSymbol {getUnitSymbol :: Symbol}
-- | Wrapper for giving names to arguments.
newtype ConcatSymbol = ConcatSymbol {getConcatSymbol :: Symbol}
-- | Wrapper for giving names to arguments.
newtype ConcreteElements variable =
    ConcreteElements {getConcreteElements :: [TermLike variable]}
-- | Wrapper for giving names to arguments.
newtype VariableElements variable =
    VariableElements {getVariableElements :: [TermLike variable]}
-- | Wrapper for giving names to arguments.
newtype Opaque variable =
    Opaque {getOpaque :: [TermLike variable]}

{- | Externalizes a 'Domain.InternalAc' as a 'TermLike'.
-}
asTermLike
    :: forall variable
    .  (Ord variable, SortedVariable variable, Unparse variable)
    => UnitSymbol
    -> ConcatSymbol
    -> ConcreteElements variable
    -> VariableElements variable
    -> Opaque variable
    -> TermLike variable
asTermLike
    (UnitSymbol unitSymbol)
    (ConcatSymbol concatSymbol)
    (ConcreteElements concreteElements)
    (VariableElements variableElements)
    (Opaque opaque)
  =
    case splitLastInit concreteElements of
        Nothing -> case splitLastInit opaque of
            Nothing -> case splitLastInit variableElements of
                Nothing -> mkApplySymbol unitSymbol []
                Just (ves, ve) -> addTerms ves ve
            Just (opaqs, opaq) ->
                addTerms variableElements (addTerms opaqs opaq)
        Just (concretes, concrete) ->
            addTerms variableElements
            $ addTerms opaque
            $ addTerms concretes concrete
  where
    addTerms :: [TermLike variable] -> TermLike variable -> TermLike variable
    addTerms terms term = List.foldr concat' term terms

    concat' :: TermLike variable -> TermLike variable -> TermLike variable
    concat' map1 map2 = mkApplySymbol concatSymbol [map1, map2]

splitLastInit :: [a] -> Maybe ([a], a)
splitLastInit [] = Nothing
splitLastInit [a] = Just ([], a)
splitLastInit (a:as) = do
    (initA, lastA) <- splitLastInit as
    return (a:initA, lastA)
