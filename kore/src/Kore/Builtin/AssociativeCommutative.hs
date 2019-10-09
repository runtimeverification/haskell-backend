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

{-# LANGUAGE UndecidableInstances #-}

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
    , renormalize
    , TermNormalizedAc
    , unifyEqualsNormalized
    , UnitSymbol(..)
    , VariableElements (..)
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT
    , partitionEithers
    )
import Control.Monad
    ( (>=>)
    )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import qualified Data.List as List
import qualified Data.List
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Reflection
    ( Given
    )
import qualified Data.Reflection as Reflection
import Data.Text.Prettyprint.Doc
    ( Doc
    )
import GHC.Stack
    ( HasCallStack
    )

import Branch
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Map.Map as Map
import qualified Kore.Builtin.Set.Set as Set
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Conditional
    ( Conditional
    , andCondition
    , withCondition
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( pattern App_
    , pattern BuiltinMap_
    , pattern BuiltinSet_
    , Concrete
    , pattern ElemVar_
    , InternalVariable
    , TermLike
    , pattern Var_
    , mkApplySymbol
    , mkBuiltin
    , mkElemVar
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Sort
    ( Sort
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.ElementVariable
    ( ElementVariable (getElementVariable)
    )
import Kore.Syntax.Variable
    ( SortedVariable
    , sortedVariableSort
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
    ( unparse
    , unparseToString
    )
import qualified Kore.Unparser as Unparser

{- | Class for things that can fill the @builtinAcChild@ value of a
@InternalAc@ struct inside a @Domain.Builtin.Builtin@ value.
-}
class
    Domain.AcWrapper (normalized :: * -> * -> *)
    => TermWrapper normalized
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
        => TermLike variable
        -> NormalizedOrBottom normalized variable

    {- | Pattern match on a 'TermLike' to return a 'normalized'.

    @matchBuiltin@ returns 'Nothing' if the 'TermLike' does not wrap a
    'normalized' value.

     -}
    matchBuiltin
        :: TermLike variable
        -> Maybe (normalized (TermLike Concrete) (TermLike variable))

    isSimplifiedValue :: Domain.Value normalized (TermLike variable) -> Bool

instance TermWrapper Domain.NormalizedMap where
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

    matchBuiltin (BuiltinMap_ internalMap) =
        Just (Domain.builtinAcChild internalMap)
    matchBuiltin _ = Nothing

    {- |Transforms a @TermLike@ representation into a @NormalizedOrBottom@.

    The map may become bottom if we had conflicts between elements that were
    not detected before, e.g.

    @
    concat({1->"a"}, concat(X:Map, {1}))
    concat(elem(Y:Int), concat({1}, elem(Y:Int)))
    concat(X:Map, concat({1}, X:Map))
    @
    -}
    toNormalized (BuiltinMap_ Domain.InternalAc { builtinAcChild }) =
        maybe Bottom Normalized (renormalize builtinAcChild)
    toNormalized (App_ symbol args)
      | Map.isSymbolUnit symbol =
        case args of
            [] -> (Normalized . Domain.wrapAc) Domain.emptyNormalizedAc
            _ -> Builtin.wrongArity "MAP.unit"
      | Map.isSymbolElement symbol =
        case args of
            [key, value]
              | Just key' <- Builtin.toKey key ->
                (Normalized . Domain.wrapAc) Domain.NormalizedAc
                    { elementsWithVariables = []
                    , concreteElements =
                        Map.singleton key' (Domain.MapValue value)
                    , opaque = []
                    }
              | otherwise ->
                (Normalized . Domain.wrapAc) Domain.NormalizedAc
                    { elementsWithVariables = [Domain.MapElement (key, value)]
                    , concreteElements = Map.empty
                    , opaque = []
                    }
            _ -> Builtin.wrongArity "MAP.element"
      | Map.isSymbolConcat symbol =
        case args of
            [set1, set2] -> toNormalized set1 <> toNormalized set2
            _ -> Builtin.wrongArity "MAP.concat"
    toNormalized patt =
        (Normalized . Domain.wrapAc) Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = Map.empty
            , opaque = [patt]
            }

    isSimplifiedValue = TermLike.isSimplified . Domain.getMapValue

instance TermWrapper Domain.NormalizedSet where
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

    matchBuiltin (BuiltinSet_ internalSet) =
        Just (Domain.builtinAcChild internalSet)
    matchBuiltin _ = Nothing

    {- |Transforms a @TermLike@ representation into a @NormalizedSetOrBottom@.

    The set may become bottom if we had conflicts between elements that were
    not detected before, e.g.

    @
    concat({1}, concat(X:Set, {1}))
    concat(elem(Y:Int), concat({1}, elem(Y:Int)))
    concat(X:Set, concat({1}, X:Set))
    @
    -}
    toNormalized (BuiltinSet_ Domain.InternalAc { builtinAcChild }) =
        maybe Bottom Normalized (renormalize builtinAcChild)
    toNormalized (App_ symbol args)
      | Set.isSymbolUnit symbol =
        case args of
            [] -> (Normalized . Domain.wrapAc) Domain.emptyNormalizedAc
            _ -> Builtin.wrongArity "SET.unit"
      | Set.isSymbolElement symbol =
        case args of
            [elem1]
              | Just elem1' <- Builtin.toKey elem1 ->
                (Normalized . Domain.wrapAc) Domain.NormalizedAc
                    { elementsWithVariables = []
                    , concreteElements = Map.singleton elem1' Domain.SetValue
                    , opaque = []
                    }
              | otherwise ->
                (Normalized . Domain.wrapAc) Domain.NormalizedAc
                    { elementsWithVariables = [Domain.SetElement elem1]
                    , concreteElements = Map.empty
                    , opaque = []
                    }
            _ -> Builtin.wrongArity "SET.element"
      | Set.isSymbolConcat symbol =
        case args of
            [set1, set2] -> toNormalized set1 <> toNormalized set2
            _ -> Builtin.wrongArity "SET.concat"
    toNormalized patt =
        (Normalized . Domain.wrapAc) Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements = Map.empty
            , opaque = [patt]
            }

    isSimplifiedValue Domain.SetValue = True

{- | Wrapper for terms that keeps the "concrete" vs "with variable" distinction
after converting @TermLike Concrete@ to @TermLike variable@.
-}
data ConcreteOrWithVariable normalized variable
    = ConcretePat (TermLike variable, Domain.Value normalized (TermLike variable))
    | WithVariablePat (TermLike variable, Domain.Value normalized (TermLike variable))

fromConcreteOrWithVariable
    :: ConcreteOrWithVariable normalized variable
    -> (TermLike variable, Domain.Value normalized (TermLike variable))
fromConcreteOrWithVariable (ConcretePat result) = result
fromConcreteOrWithVariable (WithVariablePat result) = result

{- | Particularizes @Domain.NormalizedAc@ to the most common types.
-}
type TermNormalizedAc normalized variable =
    normalized (TermLike Concrete) (TermLike variable)

{-| A normalized representation of an associative-commutative structure that
also allows bottom values.
-}
data NormalizedOrBottom collection variable
    = Normalized (TermNormalizedAc collection variable)
    | Bottom

deriving instance
    Eq (TermNormalizedAc collection variable)
    => Eq (NormalizedOrBottom collection variable)

deriving instance
    Ord (TermNormalizedAc collection variable)
    => Ord (NormalizedOrBottom collection variable)

deriving instance
    Show (TermNormalizedAc collection variable)
    => Show (NormalizedOrBottom collection variable)

{- | The semigroup defined by the `concat` operation.
-}
instance
    (Ord variable, TermWrapper normalized)
    => Semigroup (NormalizedOrBottom normalized variable)
  where
    Bottom <> _ = Bottom
    _ <> Bottom = Bottom
    Normalized normalized1 <> Normalized normalized2 =
        maybe Bottom Normalized $ concatNormalized normalized1 normalized2

concatNormalized
    :: forall normalized variable
    .  (TermWrapper normalized, Ord variable)
    => normalized (TermLike Concrete) (TermLike variable)
    -> normalized (TermLike Concrete) (TermLike variable)
    -> Maybe (normalized (TermLike Concrete) (TermLike variable))
concatNormalized normalized1 normalized2 = do
    Monad.guard disjointConcreteElements
    abstract' <-
        updateAbstractElements $ onBoth (++) Domain.elementsWithVariables
    let concrete' = onBoth Map.union Domain.concreteElements
        opaque'   = Data.List.sort $ onBoth (++) Domain.opaque
    renormalize $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = abstract'
        , concreteElements = concrete'
        , opaque = opaque'
        }
  where
    onBoth
        ::  (a -> a -> r)
        ->  (   Domain.NormalizedAc
                    normalized
                    (TermLike Concrete)
                    (TermLike variable)
            ->  a
            )
        -> r
    onBoth f g = Function.on f (g . Domain.unwrapAc) normalized1 normalized2
    disjointConcreteElements =
        null $ onBoth Map.intersection Domain.concreteElements

{- | Take a (possibly de-normalized) internal representation to its normal form.

@renormalize@ returns 'Nothing' if the normal form is @\\bottom@.

First, abstract elements are converted to concrete elements wherever
possible. Second, any opaque terms which are actually builtins are combined with
the top-level term, so that the normal form never has children which are
internal representations themselves; this "flattening" step also recurses to
@renormalize@ the previously-opaque children.

 -}
renormalize
    :: (TermWrapper normalized, Ord variable)
    => normalized (TermLike Concrete) (TermLike variable)
    -> Maybe (normalized (TermLike Concrete) (TermLike variable))
renormalize = normalizeAbstractElements >=> flattenOpaque

-- | Insert the @key@-@value@ pair if it is missing from the 'Map'.
insertMissing
    :: Ord key
    => key
    -> value
    -> Map key value
    -> Maybe (Map key value)
insertMissing k v m
  | Map.member k m = Nothing
  | otherwise      = Just (Map.insert k v m)

{- | Insert the new concrete elements into the 'Map'.

Return 'Nothing' if there are any duplicate keys.

 -}
updateConcreteElements
    :: Ord key
    => Map key value
    -> [(key, value)]
    -> Maybe (Map key value)
updateConcreteElements = Foldable.foldrM (uncurry insertMissing)

{- | Sort the abstract elements.

Return 'Nothing' if there are any duplicate keys.

 -}
updateAbstractElements
    :: (Domain.AcWrapper collection, Ord child)
    => [Domain.Element collection child]
    -> Maybe [Domain.Element collection child]
updateAbstractElements elements =
    fmap (map Domain.wrapElement . Map.toList)
    $ Foldable.foldrM (uncurry insertMissing) Map.empty
    $ map Domain.unwrapElement elements

{- | Make any abstract elements into concrete elements if possible.

Return 'Nothing' if there are any duplicate (concrete or abstract) keys.

 -}
normalizeAbstractElements
    :: (TermWrapper normalized, Ord variable)
    => normalized (TermLike Concrete) (TermLike variable)
    -> Maybe (normalized (TermLike Concrete) (TermLike variable))
normalizeAbstractElements (Domain.unwrapAc -> normalized) = do
    concrete' <- updateConcreteElements concrete newConcrete
    abstract' <- updateAbstractElements newAbstract
    return $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = abstract'
        , concreteElements = concrete'
        , opaque = Domain.opaque normalized
        }
  where
    abstract = Domain.elementsWithVariables normalized
    concrete = Domain.concreteElements normalized
    (newConcrete, newAbstract) =
        partitionEithers (extractConcreteElement <$> abstract)

-- | 'Left' if the element's key can be concretized, or 'Right' if it
-- remains abstract.
extractConcreteElement
    ::  Domain.AcWrapper collection
    =>  Domain.Element collection (TermLike variable)
    ->  Either
            (TermLike Concrete, Domain.Value collection (TermLike variable))
            (Domain.Element collection (TermLike variable))
extractConcreteElement element =
    maybe (Right element) (Left . flip (,) value) (Builtin.toKey key)
  where
    (key, value) = Domain.unwrapElement element

{- | Move any @normalized@ children to the top-level by concatenation.

@flattenOpaque@ recursively flattens the children of children, and so on.

 -}
flattenOpaque
    :: (TermWrapper normalized, Ord variable)
    => normalized (TermLike Concrete) (TermLike variable)
    -> Maybe (normalized (TermLike Concrete) (TermLike variable))
flattenOpaque (Domain.unwrapAc -> normalized) = do
    let opaque = Domain.opaque normalized
        (builtin, opaque') = partitionEithers (extractBuiltin <$> opaque)
        transparent = Domain.wrapAc normalized { Domain.opaque = opaque' }
    Foldable.foldrM concatNormalized transparent builtin
  where
    extractBuiltin termLike =
        maybe (Right termLike) Left (matchBuiltin termLike)

{- | The monoid defined by the `concat` and `unit` operations.
-}
instance
    (Ord variable, TermWrapper normalized)
    => Monoid (NormalizedOrBottom normalized variable)
  where
    mempty = Normalized $ Domain.wrapAc Domain.emptyNormalizedAc

{- | Computes the union of two maps if they are disjoint. Returns @Nothing@
otherwise.
-}
addToMapDisjoint
    :: (Ord a, Traversable t) => Map a b -> t (a, b) -> Maybe (Map a b)
addToMapDisjoint existing traversable = do
    (_, mapResult) <- Monad.foldM addElementDisjoint ([], existing) traversable
    return mapResult

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
        , InternalVariable variable
        , TermWrapper normalized
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
        , InternalVariable variable
        , TermWrapper normalized
        )
    => Sort
    -> Map (TermLike Concrete) (Domain.Value normalized (TermLike variable))
    -> m (AttemptedAxiom variable)
returnConcreteAc resultSort concrete =
    returnAc resultSort
    $ Domain.wrapAc Domain.NormalizedAc
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
    :: (InternalVariable variable, TermWrapper normalized)
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> TermNormalizedAc normalized variable
    -> TermLike variable
asInternal tools builtinAcSort builtinAcChild =
    mkBuiltin $ asInternalBuiltin tools builtinAcSort builtinAcChild

{- | The same as 'asInternal', but for ac structures made only of concrete
elements.
-}
asInternalConcrete
    :: (InternalVariable variable, TermWrapper normalized)
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Map (TermLike Concrete) (Domain.Value normalized (TermLike variable))
    -> TermLike variable
asInternalConcrete tools sort1 concreteAc =
    asInternal tools sort1
    $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = []
        , concreteElements = concreteAc
        , opaque = []
        }

elementListAsInternal
    :: forall normalized variable
    .  (InternalVariable variable, TermWrapper normalized)
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> [(TermLike variable, Domain.Value normalized (TermLike variable))]
    -> Maybe (TermLike variable)
elementListAsInternal tools sort1 terms = do
    (asInternal tools sort1 . Domain.wrapAc)
    <$> elementListAsNormalized terms

elementListAsNormalized
    :: forall normalized variable
    .  (InternalVariable variable, TermWrapper normalized)
    => [(TermLike variable, Domain.Value normalized (TermLike variable))]
    -> Maybe
        (Domain.NormalizedAc normalized (TermLike Concrete) (TermLike variable))
elementListAsNormalized terms = do
    let (withVariables, concrete) = splitVariableConcrete terms
    _checkDisjoinVariables <- disjointMap withVariables
    concreteAc <- disjointMap concrete
    return Domain.NormalizedAc
        { elementsWithVariables = Domain.wrapElement <$> withVariables
        , concreteElements = concreteAc
        , opaque = []
        }

{- | Render a 'NormalizedAc' as an extended domain value pattern.
-}
asPattern
    ::  ( InternalVariable variable
        , Given (SmtMetadataTools Attribute.Symbol)
        , TermWrapper normalized
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
    :: forall m normalized variable
    .   ( MonadSimplify m
        , InternalVariable variable
        , TermWrapper normalized
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
    maybe (return emptyAttemptedAxiom) (returnAc resultSort)
    $ concatNormalized normalized1 normalized2


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
    :: forall normalized unifier variable
    .   ( SimplifierVariable variable
        , Traversable (Domain.Value normalized)
        , TermWrapper normalized
        , MonadUnify unifier
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
        Domain.InternalAc { builtinAcChild = firstNormalized } =
            normalized1
        Domain.InternalAc { builtinAcChild = secondNormalized } =
            normalized2

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
        unifierTerm = markSimplified $ asInternal tools sort1 renormalized

        markSimplified
          | all TermLike.isSimplified opaque
          , all TermLike.isSimplified abstractKeys
          , all isSimplifiedValue abstractValues
          , all TermLike.isSimplified concreteKeys
          , all isSimplifiedValue concreteValues
          = TermLike.markSimplified
          | otherwise
          = id
          where
            unwrapped = Domain.unwrapAc renormalized
            Domain.NormalizedAc { opaque } = unwrapped
            (abstractKeys, abstractValues) =
                (unzip . map Domain.unwrapElement)
                    (Domain.elementsWithVariables unwrapped)
            (concreteKeys, concreteValues) =
                (unzip . Map.toList)
                    (Domain.concreteElements unwrapped)

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
        case toNormalized patt of
            Bottom -> Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                "Duplicated elements in normalization."
                first
                second
            Normalized n -> return n

{- | Unifies two AC structs represented as @NormalizedAc@.

Currently allows at most one opaque term in the two arguments taken together.
-}
unifyEqualsNormalizedAc
    ::  forall normalized variable unifier
    .   ( SimplifierVariable variable
        , Traversable (Domain.Value normalized)
        , TermWrapper normalized
        , MonadUnify unifier
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
    normalized1
    normalized2
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
        ([ElemVar_ v1], _)
          | null allElements1 ->
            unifyOpaqueVariable' v1 allElements2 opaqueDifference2
        (_, [ElemVar_ v2])
          | null allElements2 ->
            unifyOpaqueVariable' v2 allElements1 opaqueDifference1
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

    unifyOpaqueVariable' =
        unifyOpaqueVariable tools bottomWithExplanation unifyEqualsChildren

    Domain.NormalizedAc
        { elementsWithVariables = preElementsWithVariables1
        , concreteElements = concreteElements1
        , opaque = opaque1
        }
        = Domain.unwrapAc normalized1
    Domain.NormalizedAc
        { elementsWithVariables = preElementsWithVariables2
        , concreteElements = concreteElements2
        , opaque = opaque2
        }
        = Domain.unwrapAc normalized2

    opaque1Map = listToMap opaque1
    opaque2Map = listToMap opaque2

    elementsWithVariables1 = Domain.unwrapElement <$> preElementsWithVariables1
    elementsWithVariables2 = Domain.unwrapElement <$> preElementsWithVariables2
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
        :: (TermLike Concrete, Domain.Value normalized (TermLike variable))
        -> ConcreteOrWithVariable normalized variable
    toConcretePat (a, b) = ConcretePat (TermLike.fromConcrete a, b)

    unifyElementList
        :: forall key
        .   [
                (key
                ,   ( Domain.Value normalized (TermLike variable)
                    , Domain.Value normalized (TermLike variable)
                    )
                )
            ]
        -> unifier
            ( [(key, Domain.Value normalized (TermLike variable))]
            , Predicate variable
            )
    unifyElementList elements = do
        result <- mapM (unifyCommonElements unifyEqualsChildren) elements
        let
            terms :: [(key, Domain.Value normalized (TermLike variable))]
            predicates :: [Predicate variable]
            (terms, predicates) = unzip (map Conditional.splitTerm result)
            predicate :: Predicate variable
            predicate = List.foldl'
                andCondition
                Predicate.top
                predicates

        return (terms, predicate)

    simplify :: TermLike variable -> unifier (Pattern variable)
    simplify term = alternate $ simplifyConditionalTerm Predicate.top term

    simplifyPair
        :: (TermLike variable, Domain.Value normalized (TermLike variable))
        -> unifier
            (Conditional
                variable
                (TermLike variable, Domain.Value normalized (TermLike variable))
            )
    simplifyPair (key, value) = do
        simplifiedKey <- simplifyTermLike key
        let (keyTerm, keyPredicate) = Conditional.splitTerm simplifiedKey
        simplifiedValue <- traverse simplifyTermLike value
        let
            splitSimplifiedValue
                :: Domain.Value
                    normalized
                    (TermLike variable, Predicate variable)
            splitSimplifiedValue =
                fmap Conditional.splitTerm simplifiedValue
            simplifiedValueTerm :: Domain.Value normalized (TermLike variable)
            simplifiedValueTerm = fmap fst splitSimplifiedValue
            simplifiedValuePredicates
                :: Domain.Value normalized (Predicate variable)
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
            alternate $ simplifyConditionalTerm Predicate.top term

buildResultFromUnifiers
    :: forall normalized unifier variable
    .   ( Monad unifier
        , InternalVariable variable
        , TermWrapper normalized
        )
    => (forall result . Doc () -> unifier result)
    -> [(TermLike Concrete, Domain.Value normalized (TermLike variable))]
    -> [(TermLike variable, Domain.Value normalized (TermLike variable))]
    -> [TermLike variable]
    ->  [ Conditional
            variable
            (TermLike variable, Domain.Value normalized (TermLike variable))
        ]
    -> [Pattern variable]
    -> [Predicate variable]
    -> unifier (Conditional variable (TermNormalizedAc normalized variable))
buildResultFromUnifiers
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
            ::  [   ( TermLike variable
                    , Domain.Value normalized (TermLike variable)
                    )
                ]
        almostResultPredicates :: [Predicate variable]
        (almostResultTerms, almostResultPredicates) =
            unzip (map Conditional.splitTerm unifiedElementsSimplified)
        (withVariableTerms, concreteTerms) =
            splitVariableConcrete almostResultTerms

        (opaquesTerms, opaquesPredicates) =
            unzip (map Conditional.splitTerm opaquesSimplified)
        opaquesNormalized :: NormalizedOrBottom normalized variable
        opaquesNormalized = Foldable.foldMap toNormalized opaquesTerms

    Domain.NormalizedAc
        { elementsWithVariables = preOpaquesElementsWithVariables
        , concreteElements = opaquesConcreteTerms
        , opaque = opaquesOpaque
        } <- case opaquesNormalized of
            Bottom ->
                bottomWithExplanation "Duplicated elements after unification."
            Normalized result -> return (Domain.unwrapAc result)
    let opaquesElementsWithVariables =
            Domain.unwrapElement <$> preOpaquesElementsWithVariables

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
            :: Conditional variable
                (normalized (TermLike Concrete) (TermLike variable))
        result =
            Domain.wrapAc Domain.NormalizedAc
                { elementsWithVariables =
                    Domain.wrapElement <$> Map.toList withVariableMap
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
        , InternalVariable variable
        , Traversable (Domain.Value normalized)
        )
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
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
    unifier
    (key, (firstValue, secondValue))
  = do
    valuesUnifier <- unifyWrappedValues unifier firstValue secondValue
    let
        (valuesTerm, valuePredicate) = Conditional.splitTerm valuesUnifier

    return ((key, valuesTerm) `withCondition` valuePredicate)

unifyWrappedValues
    :: forall normalized unifier variable
    .   ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , InternalVariable variable
        , Traversable (Domain.Value normalized)
        )
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> Domain.Value normalized (TermLike variable)
    -> Domain.Value normalized (TermLike variable)
    ->  unifier
            (Conditional variable (Domain.Value normalized (TermLike variable)))
unifyWrappedValues unifier firstValue secondValue = do
    let aligned = Domain.alignValues firstValue secondValue
    unifiedValues <- traverse (uncurry unifier) aligned
    let
        splitValues
            :: Domain.Value normalized (TermLike variable, Predicate variable)
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
    ::  forall normalized variable unifier
    .   ( Domain.AcWrapper normalized
        , SimplifierVariable variable
        , MonadUnify unifier
        , TermWrapper normalized
        , Traversable (Domain.Value normalized)
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -- ^ unifier function
    -> [ConcreteOrWithVariable normalized variable]
    -- ^ First structure elements
    -> [ConcreteOrWithVariable normalized variable]
    -- ^ Second structure elements
    -> Maybe (TermLike variable)
    -- ^ Opaque part of the first structure
    -> unifier
        ( Conditional
            variable
            [(TermLike variable, Domain.Value normalized (TermLike variable))]
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
    Monad.unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)
    -- The first structure does not include an opaque term so there is nothing
    -- to match whatever is left in remainder2. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    Monad.unless
        (null remainder2)
        (remainderError firstElements secondElements remainder2)

    return (result, [])
  where
    unifyWithPermutations
        :: [ConcreteOrWithVariable normalized variable]
        -- ^ First structure elements
        -> [ConcreteOrWithVariable normalized variable]
        -- ^ Second structure elements
        -> unifier
            (Conditional variable
                [   ( TermLike variable
                    , Domain.Value normalized (TermLike variable)
                    )
                ]
            , [ConcreteOrWithVariable normalized variable]
            , [ConcreteOrWithVariable normalized variable]
            )
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable unifyEqualsChildren)
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
    Monad.unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)

    let remainder2Terms = map fromConcreteOrWithVariable remainder2

    case elementListAsInternal tools (termLikeSort first) remainder2Terms of
        Nothing -> Monad.Unify.explainAndReturnBottom
            "Duplicated element in unification results"
            first
            second
        Just remainderTerm -> case opaque of
            Var_ _
              | TermLike.isFunctionPattern remainderTerm -> do
                opaqueUnifier <- unifyEqualsChildren opaque remainderTerm
                let
                    (opaqueTerm, opaquePredicate) =
                        Pattern.splitTerm opaqueUnifier
                    result = unifier `andCondition` opaquePredicate

                return (result, [opaqueTerm])
            _ -> (error . unlines)
                [ "Unification case that should be handled somewhere else:"
                , "attempting normalized unification with a non-variable opaque"
                , "term or non-function maps could lead to infinite loops."
                , "first=" ++ unparseToString first
                , "second=" ++ unparseToString second
                ]

  where
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable unifyEqualsChildren)
    remainderError = nonEmptyRemainderError first second

unifyOpaqueVariable
    ::  ( MonadUnify unifier
        , TermWrapper normalized
        , SimplifierVariable variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> (forall a . Doc () -> unifier a)
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -- ^ unifier function
    -> TermLike.ElementVariable variable
    -> [ConcreteOrWithVariable normalized variable]
    -> [TermLike variable]
    -> MaybeT unifier
        ( Conditional
            variable
            [(TermLike variable, Domain.Value normalized (TermLike variable))]
        , [TermLike variable]
        )
unifyOpaqueVariable _ _ unifyChildren v1 [] [second@(ElemVar_ _)] = do
    noCheckUnifyOpaqueChildren unifyChildren v1 second
unifyOpaqueVariable
    tools
    bottomWithExplanation
    unifyChildren
    v1
    concreteOrVariableTerms
    opaqueTerms
  =
    case elementListAsNormalized pairs of
        Nothing -> Monad.Trans.lift $ bottomWithExplanation
            "Duplicated element in unification results"
        Just elementTerm ->
            let secondTerm =
                    asInternal
                        tools
                        sort
                        (Domain.wrapAc
                            elementTerm {Domain.opaque = opaqueTerms}
                        )
            in if TermLike.isFunctionPattern secondTerm
                then noCheckUnifyOpaqueChildren unifyChildren v1 secondTerm
                else empty
  where
    sort = sortedVariableSort (getElementVariable v1)
    pairs = map fromConcreteOrWithVariable concreteOrVariableTerms

noCheckUnifyOpaqueChildren
    ::  ( MonadUnify unifier
        , Ord variable
        , SortedVariable variable
        )
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermLike.ElementVariable variable
    -> TermLike variable
    -> MaybeT unifier
        ( Conditional
            variable
            [(TermLike variable, Domain.Value normalized (TermLike variable))]
        , [TermLike variable]
        )
noCheckUnifyOpaqueChildren unifyChildren v1 second = Monad.Trans.lift $ do
    unifier <- unifyChildren (mkElemVar v1) second
    let (opaque, predicate) = Conditional.splitTerm unifier
    return ([] `Conditional.withCondition` predicate, [opaque])

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
        , Traversable (Domain.Value normalized)
        , SimplifierVariable variable
        )
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> ConcreteOrWithVariable normalized variable
    -> ConcreteOrWithVariable normalized variable
    -> unifier
        (Conditional
            variable
            (TermLike variable, Domain.Value normalized (TermLike variable))
        )
unifyEqualsConcreteOrWithVariable
    unifier
    (ConcretePat concrete1)
    (ConcretePat concrete2)
  = unifyEqualsPair unifier concrete1 concrete2
unifyEqualsConcreteOrWithVariable
    unifier
    (ConcretePat concrete1)
    (WithVariablePat withVariable2)
  = unifyEqualsPair unifier concrete1 withVariable2
unifyEqualsConcreteOrWithVariable
    unifier
    (WithVariablePat withVariable1)
    (ConcretePat concrete2)
  = unifyEqualsPair unifier concrete2 withVariable1
unifyEqualsConcreteOrWithVariable
    unifier
    (WithVariablePat withVariable1)
    (WithVariablePat withVariable2)
  = unifyEqualsPair unifier withVariable1 withVariable2

unifyEqualsPair
    :: forall normalized unifier variable
    .   ( Domain.AcWrapper normalized
        , MonadUnify unifier
        , SimplifierVariable variable
        , Traversable (Domain.Value normalized)
        )
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> (TermLike variable, Domain.Value normalized (TermLike variable))
    -> (TermLike variable, Domain.Value normalized (TermLike variable))
    -> unifier
        (Conditional
            variable
            (TermLike variable, Domain.Value normalized (TermLike variable))
        )
unifyEqualsPair
    unifier
    (firstKey, firstValue)
    (secondKey, secondValue)
  = do
    keyUnifier <- unifier firstKey secondKey

    valueUnifier <- unifyWrappedValues unifier firstValue secondValue

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
        , SimplifierVariable variable
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
    :: forall a normalized variable
    .   ( HasCallStack
        , InternalVariable variable
        , Domain.AcWrapper normalized
        )
    => TermLike variable
    -> TermLike variable
    -> [ConcreteOrWithVariable normalized variable]
    -> [ConcreteOrWithVariable normalized variable]
    -> [ConcreteOrWithVariable normalized variable]
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
    unparsePair = Domain.unparseElement unparse . Domain.wrapElement

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
    .  InternalVariable variable
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
