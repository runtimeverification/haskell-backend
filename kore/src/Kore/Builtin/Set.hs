{- |
Module      : Kore.Builtin.Set
Description : Built-in sets
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Set as Set
@
 -}
module Kore.Builtin.Set
    ( sort
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    , Domain.Builtin
    , returnSet
    , asInternal
    , asPattern
    , asTermLike
    , expectBuiltinSet
      -- * Symbols
    , lookupSymbolIn
    , lookupSymbolDifference
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
      -- * Keys
    , unitKey
    , elementKey
    , concatKey
    , inKey
    , differenceKey
    , toListKey
    , sizeKey
    , intersectionKey
      -- * Unification
    , unifyEquals
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT (MaybeT), partitionEithers, runMaybeT )
import           Control.Error.Util
                 ( note )
import           Control.Monad
                 ( foldM, unless, when )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Reflection as Reflection
import qualified Data.Sequence as Seq
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import qualified Kore.Builtin.Bool as Bool
import           Kore.Builtin.Builtin
                 ( acceptAnySort )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Conditional
                 ( Conditional (Conditional), andCondition, withCondition )
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
                 mkApplySymbol, mkBuiltin, mkSort, termLikeSort )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Sort
                 ( Sort )
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.Syntax.Sentence
                 ( SentenceSort (SentenceSort) )
import qualified Kore.Syntax.Sentence as Sentence.DoNotUse
                 ( SentenceSort (..) )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparseToString )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Builtin name of the @Set@ sort.
 -}
sort :: Text
sort = "SET.Set"

{- | Verify that the sort is hooked to the builtin @Set@ sort.

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
      , Builtin.verifySymbol assertSort [acceptAnySort]
      )
    , ( unitKey
      , Builtin.verifySymbol assertSort []
      )
    , ( inKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
      )
    , ( differenceKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort]
      )
    , ( toListKey
      , Builtin.verifySymbol List.assertSort [assertSort]
      )
    , ( sizeKey
      , Builtin.verifySymbol Int.assertSort [assertSort]
      )
    , ( intersectionKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort]
      )
    ]

{- | Abort function evaluation if the argument is not a @Set@ domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented by a
    'BuiltinDomainSet', it is a bug.

 -}
expectBuiltinSet
    :: MonadSimplify m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Set (TermLike Concrete))
expectBuiltinSet ctx _set = do
    _set <- Builtin.expectNormalConcreteTerm _set
    case _set of
        Builtin_ domain ->
            case domain of
                Domain.BuiltinSet Domain.InternalSet { builtinSetChild } ->
                    return builtinSetChild
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a set"
        _ -> empty

returnSet
    :: (MonadSimplify m, Ord variable)
    => Sort
    -> Set (TermLike Concrete)
    -> m (AttemptedAxiom variable)
returnSet resultSort set = do
    tools <- Simplifier.askMetadataTools
    Builtin.appliedFunction
        $ Pattern.fromTermLike
        $ asInternal tools resultSort set

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom
            (case arguments of
                [_elem] -> do
                    _elem <- Builtin.expectNormalConcreteTerm _elem
                    returnSet resultSort (Set.singleton _elem)
                _ -> Builtin.wrongArity elementKey
            )

evalIn :: Builtin.Function
evalIn =
    Builtin.functionEvaluator evalIn0
  where
    evalIn0 :: Builtin.FunctionImplementation
    evalIn0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_elem, _set) =
                    case arguments of
                        [_elem, _set] -> (_elem, _set)
                        _ -> Builtin.wrongArity inKey
            _elem <- Builtin.expectNormalConcreteTerm _elem
            _set <- expectBuiltinSet inKey _set
            (Builtin.appliedFunction . asExpandedBoolPattern)
                (Set.member _elem _set)
      where
        asExpandedBoolPattern = Bool.asPattern resultSort

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ resultSort =
        \case
            [] -> returnSet resultSort Set.empty
            _ -> Builtin.wrongArity unitKey

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    ctx = concatKey
    evalConcat0 :: Builtin.FunctionImplementation
    evalConcat0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity concatKey
                leftIdentity = do
                    _set1 <- expectBuiltinSet ctx _set1
                    if Set.null _set1
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _set2
                        else empty
                rightIdentity = do
                    _set2 <- expectBuiltinSet ctx _set2
                    if Set.null _set2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _set1
                        else empty
                bothConcrete = do
                    _set1 <- expectBuiltinSet ctx _set1
                    _set2 <- expectBuiltinSet ctx _set2
                    if Set.null (Set.intersection _set1 _set2)
                        then returnSet resultSort (_set1 <> _set2)
                        else empty
            leftIdentity <|> rightIdentity <|> bothConcrete

evalDifference :: Builtin.Function
evalDifference =
    Builtin.functionEvaluator evalDifference0
  where
    ctx = differenceKey
    evalDifference0 :: Builtin.FunctionImplementation
    evalDifference0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity differenceKey
                rightIdentity = do
                    _set2 <- expectBuiltinSet ctx _set2
                    if Set.null _set2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _set1
                        else empty
                bothConcrete = do
                    _set1 <- expectBuiltinSet ctx _set1
                    _set2 <- expectBuiltinSet ctx _set2
                    returnSet resultSort (Set.difference _set1 _set2)
            rightIdentity <|> bothConcrete

evalToList :: Builtin.Function
evalToList = Builtin.functionEvaluator evalToList0
  where
    evalToList0 :: Builtin.FunctionImplementation
    evalToList0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _set =
                        case arguments of
                            [_set] -> _set
                            _      -> Builtin.wrongArity toListKey
            _set <- expectBuiltinSet toListKey _set
            List.returnList resultSort
                . fmap TermLike.fromConcrete
                . Seq.fromList
                . Set.toList
                $ _set

evalSize :: Builtin.Function
evalSize = Builtin.functionEvaluator evalSize0
  where
    evalSize0 :: Builtin.FunctionImplementation
    evalSize0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _set =
                        case arguments of
                            [_set] -> _set
                            _      -> Builtin.wrongArity sizeKey
            _set <- expectBuiltinSet sizeKey _set
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . toInteger
                . Set.size
                $ _set

evalIntersection :: Builtin.Function
evalIntersection =
    Builtin.functionEvaluator evalIntersection0
  where
    ctx = intersectionKey
    evalIntersection0 :: Builtin.FunctionImplementation
    evalIntersection0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity intersectionKey
            _set1 <- expectBuiltinSet ctx _set1
            _set2 <- expectBuiltinSet ctx _set2
            returnSet resultSort (Set.intersection _set1 _set2)

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (concatKey, evalConcat)
        , (elementKey, evalElement)
        , (unitKey, evalUnit)
        , (inKey, evalIn)
        , (differenceKey, evalDifference)
        , (toListKey, evalToList)
        , (sizeKey, evalSize)
        , (intersectionKey, evalIntersection)
        ]

{- | Render a 'Set' as an internal domain value pattern of the given sort.

The result sort must be hooked to the builtin @Set@ sort. The pattern will use
the internal representation of concrete 'Set' domain values; it will not use a
valid external representation. Use 'asPattern' to construct an externally-valid
pattern.

 -}
asInternal
    :: Ord variable
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Set (TermLike Concrete)
    -> TermLike variable
asInternal tools builtinSetSort builtinSetChild =
    (mkBuiltin . Domain.BuiltinSet)
        Domain.InternalSet
            { builtinSetSort
            , builtinSetUnit =
                Builtin.lookupSymbolUnit tools builtinSetSort
            , builtinSetElement =
                Builtin.lookupSymbolElement tools builtinSetSort
            , builtinSetConcat =
                Builtin.lookupSymbolConcat tools builtinSetSort
            , builtinSetChild
            }

{- | Render an 'Domain.InternalSet' as a 'TermLike' domain value.
 -}
asTermLike
    :: (Ord variable, SortedVariable variable, Unparse variable)
    => Domain.InternalSet (TermLike Concrete)
    -> TermLike variable
asTermLike builtin
  | Set.null set = unit
  | otherwise = foldr1 concat' (element <$> Foldable.toList set)
  where
    Domain.InternalSet { builtinSetChild = set } = builtin
    Domain.InternalSet { builtinSetUnit = unitSymbol } = builtin
    Domain.InternalSet { builtinSetElement = elementSymbol } = builtin
    Domain.InternalSet { builtinSetConcat = concatSymbol } = builtin

    unit = mkApplySymbol unitSymbol []
    element elem' = mkApplySymbol elementSymbol [TermLike.fromConcrete elem']
    concat' set1 set2 = mkApplySymbol concatSymbol [set1, set2]

listAsTermLike
    ::  ( Ord variable
        , SortedVariable variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> [TermLike variable]
    -> Maybe (TermLike variable)
    -> TermLike variable
listAsTermLike tools sort1 = listAsTermLikeHelper
  where
    listAsTermLikeHelper terms (Just v) = foldr concatWithElement v terms
    listAsTermLikeHelper [] Nothing = asInternal tools sort1 Set.empty
    listAsTermLikeHelper (term:terms) Nothing =
        foldr concatWithElement (element term) terms

    concatWithElement = concat' . element

    elementSymbol = Builtin.lookupSymbolElement tools sort1
    concatSymbol = Builtin.lookupSymbolConcat tools sort1
    element elem' = mkApplySymbol elementSymbol [elem']
    concat' set1 set2 = mkApplySymbol concatSymbol [set1, set2]

asTermLikeAndInternal
    :: forall variable
    .   ( Ord variable
        , SortedVariable variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> [TermLike variable]
    -> Maybe (TermLike variable)
asTermLikeAndInternal tools sort1 terms = do
    let (withVariables, concrete) = splitVariableConcrete terms
    _withVariablesSet <- disjointSet withVariables
    case concrete of
        [] -> return $ listAsTermLike tools sort1 withVariables Nothing
        _ -> do
            concreteSet <- disjointSet concrete
            let
                internalSet :: TermLike variable
                internalSet = asInternal tools sort1 concreteSet
            return $ listAsTermLike tools sort1 withVariables (Just internalSet)

disjointSet :: Ord a => [a] -> Maybe (Set a)
disjointSet input =
    if length input == Set.size set
    then Just set
    else Nothing
  where
    set = Set.fromList input

splitVariableConcrete
    :: [TermLike variable]
    -> ([TermLike variable], [TermLike Concrete])
splitVariableConcrete terms =
    partitionEithers (map toConcreteEither terms)
  where
    toConcreteEither
        :: TermLike variable
        -> Either (TermLike variable) (TermLike Concrete)
    toConcreteEither term =
        note term (TermLike.asConcrete term)

{- | Render a 'Seq' as an extended domain value pattern.

    See also: 'asPattern'

 -}
asPattern
    ::  ( Ord variable
        , Given (SmtMetadataTools Attribute.Symbol)
        )
    => Sort
    -> Set (TermLike Concrete)
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal tools resultSort
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = Reflection.given

concatKey :: IsString s => s
concatKey = "SET.concat"

elementKey :: IsString s => s
elementKey = "SET.element"

unitKey :: IsString s => s
unitKey = "SET.unit"

inKey :: IsString s => s
inKey = "SET.in"

differenceKey :: IsString s => s
differenceKey = "SET.difference"

toListKey :: IsString s => s
toListKey = "SET.set2list"

sizeKey :: IsString s => s
sizeKey = "SET.size"

intersectionKey :: IsString s => s
intersectionKey = "SET.intersection"

{- | Find the symbol hooked to @SET.get@ in an indexed module.
 -}
lookupSymbolIn
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolIn = Builtin.lookupSymbol inKey

{- | Find the symbol hooked to @SET.difference@ in an indexed module.
 -}
lookupSymbolDifference
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolDifference = Builtin.lookupSymbol differenceKey

{- | Check if the given symbol is hooked to @SET.concat@.
 -}
isSymbolConcat
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @SET.element@.
 -}
isSymbolElement
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @SET.unit@.
-}
isSymbolUnit
    :: SmtMetadataTools Hook
    -> Symbol
    -> Bool
isSymbolUnit = Builtin.isSymbol "SET.unit"

{- | A normalized representation of a set, with elements separated from
other set terms, and with concrete elements separated from non-concrete ones
-}
-- TODO(virgil): Use this as the internal representation of a set.
data NormalizedSet variable = NormalizedSet
    { elementsWithVariables :: Set (TermLike variable)
    , concreteElements :: Set (TermLike Concrete)
    , sets :: Set (TermLike variable)
    }
    deriving (Eq, Show)

data NormalizedSetOrBottom variable
    = Normalized (NormalizedSet variable)
    | Bottom
    deriving (Eq, Show)

instance Ord variable => Semigroup (NormalizedSetOrBottom variable) where
    Bottom <> _ = Bottom
    _ <> Bottom = Bottom
    Normalized NormalizedSet
        { elementsWithVariables = elementsWithVariables1
        , concreteElements = concreteElements1
        , sets = sets1
        }
      <> Normalized NormalizedSet
        { elementsWithVariables = elementsWithVariables2
        , concreteElements = concreteElements2
        , sets = sets2
        }
      = case mergeDisjoint of
        Nothing -> Bottom
        Just result -> Normalized result
      where
        mergeDisjoint = do
            withVariables <-
                addAllDisjoint elementsWithVariables1 elementsWithVariables2
            concrete <- addAllDisjoint concreteElements1 concreteElements2
            sets <- addAllDisjoint sets1 sets2
            return NormalizedSet
                { elementsWithVariables = withVariables
                , concreteElements = concrete
                , sets = sets
                }
        addAllDisjoint set1 set2 = addToSetDisjoint set1 (Set.toList set2)

{- | Computes the union of two sets if they are disjoint. Returns @Nothing@
otherwise.
-}
addToSetDisjoint :: (Ord a, Traversable t) => Set a -> t a -> Maybe (Set a)
addToSetDisjoint = foldM addElementDisjoint
  where
    addElementDisjoint :: Ord a => Set a -> a -> Maybe (Set a)
    addElementDisjoint set element =
        if element `Set.member` set
        then Nothing
        else return (Set.insert element set)

{- | Transforms a normalized set into a @TermLike@ representation.
-}
normalizedToTerm
    :: forall variable
    .   ( Ord variable
        , SortedVariable variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> NormalizedSet variable
    -> TermLike variable
normalizedToTerm
    tools
    sort1
    NormalizedSet
        { elementsWithVariables
        , concreteElements
        , sets
        }
  =
    if Set.null concreteElements
    then
        case filteredSets of
            [] -> case Set.toList elementsWithVariables of
                [] -> asInternal tools sort1 concreteElements
                (ewv : ewvs) -> addElements (element ewv) ewvs
            (set:sets1) ->
                let base = addSets set sets1
                in addElements base (Set.toList elementsWithVariables)
    else
        let baseC = asInternal tools sort1 concreteElements
            baseS = addSets baseC filteredSets
        in addElements baseS (Set.toList elementsWithVariables)
  where
    addElements :: TermLike variable -> [TermLike variable] -> TermLike variable
    addElements = List.foldr (\elem1 term -> concat' (element elem1) term)

    addSets :: TermLike variable -> [TermLike variable] -> TermLike variable
    addSets = List.foldr concat'

    filteredSets :: [TermLike variable]
    filteredSets = filter (not . isEmptySet) (Set.toList sets)

    isEmptySet :: TermLike variable -> Bool
    isEmptySet
        (Builtin_ (Domain.BuiltinSet Domain.InternalSet { builtinSetChild }))
      = Set.null builtinSetChild
    isEmptySet (App_ symbol _)
      | isSymbolUnit hookTools symbol = True
      | otherwise = False
    isEmptySet _ = False

    elementSymbol = Builtin.lookupSymbolElement tools sort1
    concatSymbol = Builtin.lookupSymbolConcat tools sort1
    element elem' = mkApplySymbol elementSymbol [elem']
    concat' set1 set2 = mkApplySymbol concatSymbol [set1, set2]

    hookTools = Attribute.Symbol.hook <$> tools

{- |Transforms a @TermLike@ representation into a @NormalizedSetOrBottom@.

The set may become bottom if we had conflicts between elements that were
not detected before, e.g.

@
concat({1}, concat(X:Set, {1}))
concat(elem(Y:Int), concat({1}, elem(Y:Int)))
concat(X:Set, concat({1}, X:Set))
@
-}
normalize
    :: Ord variable
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> NormalizedSetOrBottom variable
normalize
    _tools
    (Builtin_ (Domain.BuiltinSet Domain.InternalSet { builtinSetChild }))
  =
    Normalized NormalizedSet
        { elementsWithVariables = Set.empty
        , concreteElements = builtinSetChild
        , sets = Set.empty
        }
normalize tools (App_ symbol args)
  | isSymbolUnit hookTools symbol =
    case args of
        [] ->
            Normalized NormalizedSet
                { elementsWithVariables = Set.empty
                , concreteElements = Set.empty
                , sets = Set.empty
                }
        _ -> Builtin.wrongArity "SET.unit"
  | isSymbolElement hookTools symbol =
    case args of
        [elem1] ->
            Normalized NormalizedSet
                { elementsWithVariables = Set.singleton elem1
                , concreteElements = Set.empty
                , sets = Set.empty
                }
        _ -> Builtin.wrongArity "SET.element"
  | isSymbolConcat hookTools symbol =
    case args of
        [set1, set2] ->
            normalize tools set1 <> normalize tools set2
        _ -> Builtin.wrongArity "SET.concat"
  where
    hookTools = Attribute.Symbol.hook <$> tools
normalize _ patt =
    Normalized NormalizedSet
        { elementsWithVariables = Set.empty
        , concreteElements = Set.empty
        , sets = Set.singleton patt
        }

{- | Unifies two sets represented as @NormalizedSet@.

Currently allows at most one non-element set piece in the two arguments taken
together.
-}
unifyEqualsNormalizedSet
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> NormalizedSet variable
    -> NormalizedSet variable
    -> MaybeT unifier (Conditional variable (NormalizedSet variable))
unifyEqualsNormalizedSet
    tools
    first
    second
    unifyEqualsChildren
    NormalizedSet
        { elementsWithVariables = elementsWithVariables1
        , concreteElements = concreteElements1
        , sets = sets1
        }
    NormalizedSet
        { elementsWithVariables = elementsWithVariables2
        , concreteElements = concreteElements2
        , sets = sets2
        }
  = do
    (simpleUnifier, sets) <- case (setsDifference1, setsDifference2) of
        ([], []) -> Monad.Trans.lift $
            unifyEqualsNormalizedElements
                tools
                first
                second
                unifyEqualsChildren
                allSetElements1
                allSetElements2
                Nothing
        ([set], []) -> do
            when
                (  null elementsWithVariables1
                && null concreteElements1
                && (length sets1 == 1)
                )
                errorForOpaqueSets

            Monad.Trans.lift $
                unifyEqualsNormalizedElements
                    tools
                    first
                    second
                    unifyEqualsChildren
                    allSetElements1
                    allSetElements2
                    (Just set)
        ([], [set]) -> do
            when
                (  null elementsWithVariables2
                && null concreteElements2
                && (length sets2 == 1)
                )
                errorForOpaqueSets
            Monad.Trans.lift $
                unifyEqualsNormalizedElements
                    tools
                    first
                    second
                    unifyEqualsChildren
                    allSetElements2
                    allSetElements1
                    (Just set)
        (_, _) -> empty
    Monad.Trans.lift $ case simpleUnifier of
        Conditional
            { term = unifiedElements
            , predicate
            , substitution
            } -> do -- unifier monad
                -- simplify results so that things like inj applications that
                -- may have been broken into smaller pieces are being put
                -- back together.
                unifiedSimplified <- mapM simplify unifiedElements
                setsSimplified <- mapM simplify sets

                let
                    (almostResultTerms, almostResultPredicates) =
                        unzip (map Pattern.splitTerm unifiedSimplified)
                    (setsTerms, setsPredicates) =
                        unzip (map Pattern.splitTerm setsSimplified)
                    (withVariableTerms, concreteTerms) =
                        splitVariableConcrete almostResultTerms

                -- Add back all the common objects that were removed before
                -- unification.
                withVariableSet <-
                    addAllDisjoint commonVariables withVariableTerms
                concreteSet <-
                    addAllDisjoint commonElements concreteTerms
                setsSet <-
                    addAllDisjoint commonSets setsTerms

                let
                    incompleteResult = Conditional
                        { term = NormalizedSet
                            { elementsWithVariables = withVariableSet
                            , concreteElements = concreteSet
                            , sets = setsSet
                            }
                        , predicate
                        , substitution
                        }
                    -- Add all unification predicates to the result.
                    result =
                        List.foldl'
                            andCondition
                            incompleteResult
                            (  almostResultPredicates
                            ++ setsPredicates
                            )
                return result
  where
    commonElements = Set.intersection concreteElements1 concreteElements2
    commonVariables =
        Set.intersection elementsWithVariables1 elementsWithVariables2
    commonSets = Set.intersection sets1 sets2

    elementDifference1 =
        Set.toList (Set.difference concreteElements1 commonElements)
    elementDifference2 =
        Set.toList (Set.difference concreteElements2 commonElements)
    elementVariableDifference1 =
        Set.toList (Set.difference elementsWithVariables1 commonVariables)
    elementVariableDifference2 =
        Set.toList (Set.difference elementsWithVariables2 commonVariables)
    setsDifference1 =
        Set.toList (Set.difference sets1 commonSets)
    setsDifference2 =
        Set.toList (Set.difference sets2 commonSets)

    errorForOpaqueSets =
        (error . unlines)
            [ "Unification case that should be handled somewhere else:"
            , "attempting normalized unification with only an opaque"
            , "set could lead to infinite loops."
            , "first=" ++ unparseToString first
            , "second=" ++ unparseToString second
            ]

    allSetElements1 =
        map WithVariablePat elementVariableDifference1
        ++ map (ConcretePat . TermLike.fromConcrete) elementDifference1
    allSetElements2 =
        map WithVariablePat elementVariableDifference2
        ++ map (ConcretePat . TermLike.fromConcrete) elementDifference2

    addAllDisjoint :: Ord a => Set a -> [a] -> unifier (Set a)
    addAllDisjoint set elements =
        case addToSetDisjoint set elements of
            Nothing ->
                Monad.Unify.explainAndReturnBottom
                    "Duplicated elements after set unification."
                    first
                    second
            Just result -> return result

    simplify :: TermLike variable -> unifier (Pattern variable)
    simplify term = alternate $ simplifyConditionalTerm term Predicate.top

{- | Wrapper for terms that keeps the "concrete" vs "with variable" distinction
after converting @TermLike Concrete@ to @TermLike variable@.
-}
data ConcreteOrWithVariable variable
    = ConcretePat (TermLike variable)
    | WithVariablePat (TermLike variable)

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
    :: (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> ConcreteOrWithVariable variable
    -> ConcreteOrWithVariable variable
    -> unifier (Pattern variable)
unifyEqualsConcreteOrWithVariable
    unifier
    (ConcretePat concrete1)
    (ConcretePat concrete2)
  = unifier concrete1 concrete2
unifyEqualsConcreteOrWithVariable
    unifier
    (ConcretePat concrete1)
    (WithVariablePat withVariable2)
  = unifier concrete1 withVariable2
unifyEqualsConcreteOrWithVariable
    unifier
    (WithVariablePat withVariable1)
    (ConcretePat concrete2)
  = unifier concrete2 withVariable1
unifyEqualsConcreteOrWithVariable
    unifier
    (WithVariablePat withVariable1)
    (WithVariablePat withVariable2)
  = unifier withVariable1 withVariable2

fromConcreteOrWithVariable
    :: ConcreteOrWithVariable variable -> TermLike variable
fromConcreteOrWithVariable (ConcretePat pat) = pat
fromConcreteOrWithVariable (WithVariablePat pat) = pat

{- | Unifies two sets given their representation as a
a list of @ConcreteOrWithVariable@, with the first set being allowed
another set chunk that is treated as an opaque object and
will be sent to the unifier function (e.g. a variable) together with some part
of the second set.

The elements of the two sets are assumend to be disjoint.
-}
unifyEqualsNormalizedElements
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -- ^ unifier function
    -> [ConcreteOrWithVariable variable]
    -- ^ First set elements
    -> [ConcreteOrWithVariable variable]
    -- ^ Second set elements
    -> Maybe (TermLike variable)
    -- ^ Opaque part of the first set
    -> unifier
        ( Conditional variable [TermLike variable]
        , [TermLike variable]
        )
unifyEqualsNormalizedElements
    _tools
    first
    second
    unifyEqualsChildren
    firstElements
    secondElements
    Nothing
  | length firstElements /= length secondElements
    -- Neither the first, not the second set include an opaque term, so
    -- the listed elements form the two sets.
    --
    -- Since the two lists have different counts, their sets can
    -- never unify.
  = Monad.Unify.explainAndReturnBottom
        "Cannot unify sets with different sizes."
        first
        second
  | otherwise = do
    (result, remainder1, remainder2) <-
        unifyWithPermutations firstElements secondElements
    -- The second set does not include an opaque term so there is nothing to
    -- match whatever is left in remainder1. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)
    -- The first set does not include an opaque term so there is nothing to
    -- match whatever is left in remainder2. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder2)
        (remainderError firstElements secondElements remainder2)

    return (result, [])
  where
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable unifyEqualsChildren)
    remainderError = nonEmptyRemainderError first second
unifyEqualsNormalizedElements
    tools
    first
    second
    unifyEqualsChildren
    firstElements
    secondElements
    (Just set)
  | length firstElements > length secondElements
    -- The second set does not include an opaque term, so all the
    -- elements in the first set must be matched by elements in the second set.
    -- Since we don't have enough, we return bottom.
  = Monad.Unify.explainAndReturnBottom
        "Cannot unify sets with different sizes."
        first
        second
  | otherwise = do
    (unifier, remainder1, remainder2) <-
        unifyWithPermutations firstElements secondElements
    -- The second set does not include an opaque term so there is nothing to
    -- match whatever is left in remainder1. This should have been caught by
    -- the "length" check above so, most likely, this can be an assertion.
    unless
        (null remainder1)
        (remainderError firstElements secondElements remainder1)

    let remainder2Terms = map fromConcreteOrWithVariable remainder2

    case asTermLikeAndInternal tools (termLikeSort first) remainder2Terms of
        Nothing -> Monad.Unify.explainAndReturnBottom
            "Duplicated set element in unification results"
            first
            second
        Just remainderSet -> do
            setUnifier <- unifyEqualsChildren set remainderSet
            let (setTerm, setPredicate) = Pattern.splitTerm setUnifier

                result = unifier `andCondition` setPredicate

            return (result, [setTerm])
  where
    unifyWithPermutations =
        unifyEqualsElementPermutations
            (unifyEqualsConcreteOrWithVariable unifyEqualsChildren)
    remainderError = nonEmptyRemainderError first second

nonEmptyRemainderError
    ::  ( HasCallStack
        , SortedVariable variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
    -> [ConcreteOrWithVariable variable]
    -> [ConcreteOrWithVariable variable]
    -> [ConcreteOrWithVariable variable]
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
    unparseWrapped = unparseToString . fromConcreteOrWithVariable

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
    => (a -> b -> unifier (Pattern variable))
    -> [a]
    -> [b]
    -> unifier
        ( Conditional variable [TermLike variable]
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
    let (terms, predicates) = unzip (map Pattern.splitTerm unifiers)
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

{- | Simplify the conjunction or equality of two concrete Set domain values.

    When it is used for simplifying equality, one should separately solve the
    case ⊥ = ⊥. One should also throw away the term in the returned pattern.

    The sets are assumed to have the same sort, but this is not checked. If
    multiple sorts are hooked to the same builtin domain, the verifier should
    reject the definition.
 -}
unifyEquals
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
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
    _simplificationType  -- TODO: Use this.
    tools
    _substitutionSimplifier
    _simplifier
    _
    unifyEqualsChildren
    first
    second
  = MaybeT $ do
    unifiers <- Monad.Unify.gather (runMaybeT (unifyEquals0 first second))
    case sequence unifiers of
        Nothing -> return Nothing
        Just us -> Monad.Unify.scatter (map Just us)
  where
    -- | Unify the two argument patterns.
    unifyEquals0
        :: TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
    unifyEquals0
        (Builtin_ (Domain.BuiltinSet builtin1))
        (Builtin_ (Domain.BuiltinSet builtin2))
      =
        Monad.Trans.lift (unifyEqualsConcrete builtin1 builtin2)

    unifyEquals0 pat1 pat2 = do
        let firstNormalizedOrBottom = normalize tools pat1
            secondNormalizedOrBottom = normalize tools pat2
        firstNormalized <- case firstNormalizedOrBottom of
            Bottom -> Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                "Duplicated elements in normalization."
                first
                second
            Normalized n -> return n
        secondNormalized <- case secondNormalizedOrBottom of
            Bottom -> Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                "Duplicated elements in normalization."
                first
                second
            Normalized n -> return n

        unifierNormalized <-
            unifyEqualsNormalizedSet
                tools
                first
                second
                unifyEqualsChildren
                firstNormalized
                secondNormalized
        let
            unifierNormalizedTerm :: NormalizedSet variable
            unifierPredicate :: Predicate variable
            (unifierNormalizedTerm, unifierPredicate) =
                Conditional.splitTerm unifierNormalized
            renormalizedOrBottom :: NormalizedSetOrBottom variable
            renormalizedOrBottom =
                -- TODO(virgil): remove this ugly hack after representing all
                -- set builtins as NormalizedSet. Right now it is needed
                -- because, say, we don't always normalize before adding
                -- something to the sets.
                normalize
                    tools
                $ normalizedToTerm
                    tools
                    (termLikeSort first)
                    unifierNormalizedTerm
        case renormalizedOrBottom of
            Bottom -> Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                "Duplicated elements in renormalization."
                first
                second
            Normalized renormalized -> do
                let unifierTerm :: TermLike variable
                    unifierTerm =
                        normalizedToTerm
                            tools
                            (termLikeSort first)
                            renormalized
                return (unifierTerm `withCondition` unifierPredicate)

    -- | Unify two concrete sets
    unifyEqualsConcrete
        :: Domain.InternalSet (TermLike Concrete)
        -> Domain.InternalSet (TermLike Concrete)
        -> unifier (Pattern variable)
    unifyEqualsConcrete builtin1 builtin2
      | set1 == set2 = return unified
      | otherwise = bottomWithExplanation
      where
        Domain.InternalSet { builtinSetSort } = builtin1
        Domain.InternalSet { builtinSetChild = set1 } = builtin1
        Domain.InternalSet { builtinSetChild = set2 } = builtin2
        unified =
            Reflection.give tools
            $ asPattern builtinSetSort set1

    bottomWithExplanation :: unifier (Pattern variable)
    bottomWithExplanation = do
        Monad.Unify.explainBottom
            "Cannot unify sets with different sizes."
            first
            second
        empty
