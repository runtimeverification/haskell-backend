{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Predicate
    ( Predicate -- Constructor not exported on purpose
    , pattern PredicateAnd
    , pattern PredicateFalse
    , pattern PredicateTrue
    , compactPredicatePredicate
    , isFalse
    , depth
    , makePredicate, NotPredicate (..)
    , isPredicate
    , makeAndPredicate
    , makeMultipleAndPredicate
    , getMultiAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeExistsPredicate
    , makeMultipleExists
    , makeForallPredicate
    , makeFalsePredicate
    , makeFalsePredicate_
    , makeFloorPredicate
    , makeFloorPredicate_
    , makeIffPredicate
    , makeImpliesPredicate
    , makeInPredicate
    , makeInPredicate_
    , makeMuPredicate
    , makeNotPredicate
    , makeNuPredicate
    , makeOrPredicate
    , makeMultipleOrPredicate
    , makeTruePredicate
    , makeTruePredicate_
    , isSimplified
    , markSimplified
    , markSimplifiedConditional
    , markSimplifiedMaybeConditional
    , setSimplified
    , Kore.Internal.Predicate.forgetSimplified
    , simplifiedAttribute
    , isFreeOf
    , freeElementVariables
    , hasFreeVariable
    , mapVariables
    , stringFromPredicate
    , coerceSort
    , predicateSort
    , fromPredicate
    , unwrapPredicate
    , wrapPredicate
    , substitute
    ) where

import Prelude.Kore

import Data.Containers.ListUtils
    ( nubOrd
    )
import qualified Data.Either as Either
import Data.Functor.Foldable
    ( Base
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict
    ( Map
    )
import Data.Set
    ( Set
    )

import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Pattern as Attribute.Pattern
    ( simplifiedAttribute
    )
import qualified Kore.Attribute.Pattern as Attribute
    ( Pattern (Pattern)
    , Simplified
    )
import qualified Kore.Attribute.Pattern as Attribute.Pattern.DoNotUse
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike hiding
    ( depth
    , hasFreeVariable
    , isSimplified
    , mapVariables
    , markSimplified
    , markSimplifiedConditional
    , markSimplifiedMaybeConditional
    , setSimplified
    , simplifiedAttribute
    , substitute
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance TopBottom patt => TopBottom (GenericPredicate patt) where
    isTop (GenericPredicate patt) = isTop patt
    isBottom (GenericPredicate patt) = isBottom patt

instance
    (Ord variable, Unparse variable)
    => Unparse (GenericPredicate (TermLike variable))
  where
    unparse predicate =
        unparseAssoc'
            ("\\and" <> parameters [sort])
            (unparse (mkTop sort :: TermLike variable))
            (worker <$> getMultiAndPredicate predicate)
      where
        worker (GenericPredicate termLike) = unparse termLike
        sort =
            termLikeSort termLike
          where
            GenericPredicate termLike = predicate
    unparse2 (GenericPredicate pattern') = unparse2 pattern'


{-| 'Predicate' is a user-visible representation for predicates.
-}
type Predicate variable = GenericPredicate (TermLike variable)

instance InternalVariable variable => SQL.Column (Predicate variable) where
    defineColumn tableName _ =
        SQL.defineColumn tableName (SQL.Proxy @(TermLike variable))
    toColumn (GenericPredicate termLike) = SQL.toColumn termLike

instance From (Predicate variable) (TermLike variable) where
    from = unwrapPredicate
    {-# INLINE from #-}

{- 'compactPredicatePredicate' removes one level of 'GenericPredicate' which
sometimes occurs when, say, using Predicates as Traversable.
-}
compactPredicatePredicate
    :: GenericPredicate (GenericPredicate a) -> GenericPredicate a
compactPredicatePredicate (GenericPredicate x) = x

{- 'stringFromPredicate' extracts a string from a GenericPredicate,
useful in tests. This could be replaced by a generic extractor, but, for now,
treating it as an opaque entity seems useful.
-}
stringFromPredicate :: GenericPredicate String -> String
stringFromPredicate (GenericPredicate x) = x

{- 'wrapPredicate' wraps a pattern in a GenericPredicate. This is intended for
predicate evaluation and tests and should not be used outside of that.

We should consider deleting this and implementing the functionality otherwise.
-}
wrapPredicate :: TermLike variable -> Predicate variable
wrapPredicate = GenericPredicate

{- | Unwrap a 'GenericPredicate'.

This is intended for predicate evaluation and tests and should not be used
outside of that.  We should consider deleting this and implementing the
functionality otherwise.

 -}
unwrapPredicate :: Predicate variable -> TermLike variable
unwrapPredicate (GenericPredicate p) = p

{- | Return the 'TermLike' corresponding to the given 'Predicate'.

In practice, predicates are flexibly-sorted; the sort argument is used to force
the resulting pattern into a particular sort.

 -}
fromPredicate
    :: (InternalVariable variable, HasCallStack)
    => Sort  -- ^ Sort of resulting pattern
    -> Predicate variable
    -> TermLike variable
fromPredicate sort (GenericPredicate p) = TermLike.forceSort sort p

{- | Change a 'Predicate' from one 'Sort' to another.

This is a safe operation because predicates are flexibly sorted.

 -}
coerceSort
    :: (HasCallStack, InternalVariable variable)
    => Sort
    -> Predicate variable
    -> Predicate variable
coerceSort sort = fmap (TermLike.fullyOverrideSort sort)

predicateSort :: Predicate variable -> Sort
predicateSort = termLikeSort . unwrapPredicate

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate variable

pattern PredicateFalse <- GenericPredicate (Recursive.project -> _ :< BottomF _)
pattern PredicateTrue  <- GenericPredicate (Recursive.project -> _ :< TopF _)

pattern PredicateAnd
    :: Predicate variable -> Predicate variable -> Predicate variable
pattern PredicateAnd p1 p2 <-
    GenericPredicate (And_ _ (GenericPredicate -> p1) (GenericPredicate -> p2))
{-|'isFalse' checks whether a predicate is obviously bottom.
-}
isFalse :: TopBottom patt => GenericPredicate patt -> Bool
isFalse = isBottom

binaryOperator
    :: (HasCallStack, InternalVariable variable)
    => (TermLike variable -> TermLike  variable -> TermLike  variable)
    -> Predicate variable -> Predicate variable -> Predicate variable
binaryOperator operator (GenericPredicate first) (GenericPredicate second) =
    GenericPredicate (operator first sortedSecond)
  where
    sortedSecond = TermLike.fullyOverrideSort (termLikeSort first) second

{-| 'makeMultipleAndPredicate' combines a list of Predicates with 'and',
doing some simplification.
-}

makeMultipleAndPredicate
    :: (HasCallStack, InternalVariable variable)
    => [Predicate variable]
    -> Predicate variable
makeMultipleAndPredicate =
    foldl' makeAndPredicate makeTruePredicate_ . nubOrd
    -- 'and' is idempotent so we eliminate duplicates

{- | Flatten a 'Predicate' with 'And' at the top.
'getMultiAndPredicate' is the inverse of 'makeMultipleAndPredicate', up to
associativity.
 -}

getMultiAndPredicate
    :: Predicate variable
    -> [Predicate variable]
getMultiAndPredicate original@(GenericPredicate termLike) =
    case termLike of
        And_ _ left right ->
            concatMap (getMultiAndPredicate . GenericPredicate) [left, right]
        _ -> [original]

{-| 'makeMultipleOrPredicate' combines a list of Predicates with 'or',
doing some simplification.
-}
makeMultipleOrPredicate
    :: InternalVariable variable
    => [Predicate variable]
    -> Predicate variable
makeMultipleOrPredicate =
    foldl' makeOrPredicate makeFalsePredicate_ . nubOrd
    -- 'or' is idempotent so we eliminate duplicates

{-| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
-}
makeAndPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeAndPredicate b@PredicateFalse _ = b
makeAndPredicate _ b@PredicateFalse = b
makeAndPredicate PredicateTrue second = second
makeAndPredicate first PredicateTrue = first
makeAndPredicate first second
  | first == second = first
  | otherwise =
    binaryOperator TermLike.mkAnd first second

{-| 'makeOrPredicate' combines two Predicates with an 'or', doing
some simplification.
-}
makeOrPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeOrPredicate t@PredicateTrue _ = t
makeOrPredicate _ t@PredicateTrue = t
makeOrPredicate PredicateFalse second = second
makeOrPredicate first PredicateFalse = first
makeOrPredicate first second
  | first == second = first
  | otherwise =
    binaryOperator TermLike.mkOr first second

{-| 'makeImpliesPredicate' combines two Predicates into an
implication, doing some simplification.
-}
makeImpliesPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeImpliesPredicate PredicateFalse _ = makeTruePredicate_
makeImpliesPredicate _ t@PredicateTrue = t
makeImpliesPredicate PredicateTrue second = second
makeImpliesPredicate first PredicateFalse = makeNotPredicate first
makeImpliesPredicate first second =
    binaryOperator TermLike.mkImplies first second

{-| 'makeIffPredicate' combines two evaluated with an 'iff', doing
some simplification.
-}
makeIffPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeIffPredicate PredicateFalse second = makeNotPredicate second
makeIffPredicate PredicateTrue second = second
makeIffPredicate first PredicateFalse = makeNotPredicate first
makeIffPredicate first PredicateTrue = first
makeIffPredicate first second =
    binaryOperator TermLike.mkIff first second

{-| 'makeNotPredicate' negates an evaluated Predicate, doing some
simplification.
-}
makeNotPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
makeNotPredicate PredicateFalse = makeTruePredicate_
makeNotPredicate PredicateTrue  = makeFalsePredicate_
makeNotPredicate (GenericPredicate predicate) =
    GenericPredicate $ TermLike.mkNot predicate

{-| 'makeEqualsPredicate_' combines two patterns with equals, producing a
predicate.
-}
makeEqualsPredicate_
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate_ first second =
    GenericPredicate $ TermLike.mkEquals_ first second

makeEqualsPredicate
    :: InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate sort first second =
    GenericPredicate $ TermLike.mkEquals sort first second

{-| 'makeInPredicate_' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate_
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate_ first second =
    GenericPredicate $ TermLike.mkIn_ first second

{-| 'makeInPredicate_' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    :: InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate sort first second =
    GenericPredicate $ TermLike.mkIn sort first second

{-| 'makeCeilPredicate_' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate_
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeCeilPredicate_ patt =
    GenericPredicate $ TermLike.mkCeil_ patt

makeCeilPredicate
    :: InternalVariable variable
    => Sort
    -> TermLike variable
    -> Predicate variable
makeCeilPredicate sort patt =
    GenericPredicate $ TermLike.mkCeil sort patt

{-| 'makeFloorPredicate_' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate_
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeFloorPredicate_ patt =
    GenericPredicate $ TermLike.mkFloor_ patt

makeFloorPredicate
    :: InternalVariable variable
    => Sort
    -> TermLike variable
    -> Predicate variable
makeFloorPredicate sort patt =
    GenericPredicate $ TermLike.mkFloor sort patt

{-| Existential quantification for the given variable in the given predicate.
-}
makeExistsPredicate
    :: InternalVariable variable
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeExistsPredicate _ p@PredicateFalse = p
makeExistsPredicate _ t@PredicateTrue = t
makeExistsPredicate v (GenericPredicate p) =
    GenericPredicate $ TermLike.mkExists v p

{- | Existentially-quantify the given variables over the predicate.
 -}
makeMultipleExists
    :: (Foldable f, InternalVariable variable)
    => f (ElementVariable variable)
    -> Predicate variable
    -> Predicate variable
makeMultipleExists vars phi =
    foldr makeExistsPredicate phi vars

{-| Universal quantification for the given variable in the given predicate.
-}
makeForallPredicate
    :: InternalVariable variable
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeForallPredicate _ p@PredicateFalse = p
makeForallPredicate _ t@PredicateTrue = t
makeForallPredicate v (GenericPredicate p) =
    GenericPredicate $ TermLike.mkForall v p

{-| Mu quantification for the given variable in the given predicate.
-}
makeMuPredicate
    :: InternalVariable variable
    => SetVariable variable
    -> Predicate variable
    -> Predicate variable
makeMuPredicate _ p@PredicateFalse = p
makeMuPredicate _ t@PredicateTrue = t
makeMuPredicate v (GenericPredicate p) =
    GenericPredicate $ TermLike.mkMu v p

{-| Nu quantification for the given variable in the given predicate.
-}
makeNuPredicate
    :: InternalVariable variable
    => SetVariable variable
    -> Predicate variable
    -> Predicate variable
makeNuPredicate _ p@PredicateFalse = p
makeNuPredicate _ t@PredicateTrue = t
makeNuPredicate v (GenericPredicate p) =
    GenericPredicate $ TermLike.mkNu v p

{-| 'makeTruePredicate_' produces a predicate wrapping a 'top'.
-}
makeTruePredicate_ :: InternalVariable variable => Predicate variable
makeTruePredicate_ = GenericPredicate TermLike.mkTop_

makeTruePredicate :: InternalVariable variable => Sort -> Predicate variable
makeTruePredicate sort = GenericPredicate (TermLike.mkTop sort)

{-| 'makeFalsePredicate_' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate_ :: InternalVariable variable => Predicate variable
makeFalsePredicate_ = GenericPredicate TermLike.mkBottom_

makeFalsePredicate :: InternalVariable variable => Sort -> Predicate variable
makeFalsePredicate sort = GenericPredicate (TermLike.mkBottom sort)

{-| When transforming a term into a predicate, this tells
whether the predicate is different in a significant way from the term used
to build it, i.e. whether it changed when being transformed.

A significant change is a change that does not involve sorts. When building
predicates from terms we replace existing sorts with a placeholder,
assuming that later we will put the right sorts back, so we don't count
that as a significant change.
-}
data HasChanged = Changed | NotChanged
    deriving (Show, Eq)

instance Semigroup HasChanged where
    NotChanged <> x = x
    Changed <> _ = Changed

instance Monoid HasChanged where
    mempty = NotChanged

newtype NotPredicate variable
    = NotPredicate (TermLikeF variable (Predicate variable))
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => Pretty (NotPredicate variable) where
    pretty (NotPredicate termLikeF) =
        Pretty.vsep
        [ "Expected a predicate, but found:"
        , Pretty.indent 4 (unparse termLikeF)
        ]

makePredicate
    :: forall variable
    .  InternalVariable variable
    => TermLike variable
    -> Either (NotPredicate variable) (Predicate variable)
makePredicate t = fst <$> makePredicateWorker t
  where
    makePredicateWorker
        :: TermLike variable
        -> Either (NotPredicate variable) (Predicate variable, HasChanged)
    makePredicateWorker =
        Recursive.elgot makePredicateBottomUp makePredicateTopDown

    makePredicateBottomUp
        :: Base
            (TermLike variable)
            (Either (NotPredicate variable) (Predicate variable, HasChanged))
        -> Either (NotPredicate variable) (Predicate variable, HasChanged)
    makePredicateBottomUp termE = do
        termWithChanged <- sequence termE
        let dropChanged
                :: (Predicate variable, HasChanged) -> Predicate variable
            dropChanged = fst

            term@(attrs :< patE) = dropChanged <$> termWithChanged

            termSort = case attrs of
                Attribute.Pattern {patternSort} -> patternSort

            dropPredicate :: (Predicate variable, HasChanged) -> HasChanged
            dropPredicate = snd

            childChanged :: HasChanged
            childChanged = foldMap dropPredicate termWithChanged
        predicate <- case patE of
            TopF _ -> return (makeTruePredicate termSort)
            BottomF _ -> return (makeFalsePredicate termSort)
            AndF p -> return $ makeAndPredicate (andFirst p) (andSecond p)
            OrF p -> return $ makeOrPredicate (orFirst p) (orSecond p)
            IffF p -> return $ makeIffPredicate (iffFirst p) (iffSecond p)
            ImpliesF p -> return $
                makeImpliesPredicate (impliesFirst p) (impliesSecond p)
            NotF p -> return $ makeNotPredicate (notChild p)
            ExistsF p -> return $
                makeExistsPredicate (existsVariable p) (existsChild p)
            ForallF p -> return $
                makeForallPredicate (forallVariable p) (forallChild p)
            p -> Left (NotPredicate p)
        return
            (keepSimplifiedAndUpdateChanged
                childChanged
                (fmap unwrapPredicate term)
                predicate
            )

    makePredicateTopDown
        :: TermLike variable
        -> Either
            (Either (NotPredicate variable) (Predicate variable, HasChanged))
            (Base (TermLike variable) (TermLike variable))
    makePredicateTopDown (Recursive.project -> projected@(attrs :< pat)) =
        case pat of
            CeilF Ceil { ceilChild } ->
                (Left . pure)
                    ( keepSimplifiedAndUpdateChanged'
                    $ makeCeilPredicate termSort ceilChild
                    )
            FloorF Floor { floorChild } ->
                (Left . pure)
                    ( keepSimplifiedAndUpdateChanged'
                    $ makeFloorPredicate termSort floorChild
                    )
            EqualsF Equals { equalsFirst, equalsSecond } ->
                (Left . pure)
                    ( keepSimplifiedAndUpdateChanged'
                    $ makeEqualsPredicate termSort equalsFirst equalsSecond
                    )
            InF In { inContainedChild, inContainingChild } ->
                (Left . pure)
                    ( keepSimplifiedAndUpdateChanged'
                    $ makeInPredicate termSort
                        inContainedChild
                        inContainingChild
                    )
            _ -> Right projected
      where
        keepSimplifiedAndUpdateChanged' =
            keepSimplifiedAndUpdateChanged NotChanged projected
        termSort = case attrs of
            Attribute.Pattern {patternSort} -> patternSort

    keepSimplifiedAndUpdateChanged
        :: HasChanged
        -> Base (TermLike variable) (TermLike variable)
        -> Predicate variable
        -> (Predicate variable, HasChanged)
    keepSimplifiedAndUpdateChanged hasChanged termBase predicate =
        (keepSimplified newHasChanged termBase predicate, newHasChanged)
      where
        term = Recursive.embed termBase
        newHasChanged = updateHasChanged hasChanged term predicate

    keepSimplified
        :: HasChanged
        -> Base (TermLike variable) (TermLike variable)
        -> Predicate variable
        -> Predicate variable
    keepSimplified hasChanged (attrs :< _) predicate =
        case hasChanged of
            Changed -> predicate
            NotChanged -> setSimplified simplified predicate
      where
        simplified =
            Attribute.Pattern.simplifiedAttribute attrs

    updateHasChanged
        :: HasChanged
        -> TermLike variable
        -> Predicate variable
        -> HasChanged
    updateHasChanged before term predicate =
        case before of
            Changed -> Changed
            NotChanged
                | didNotChange -> NotChanged
                | otherwise -> Changed
      where
        didNotChange =
            (==)
                (TermLike.forceSort
                    (termLikeSort term)
                    (unwrapPredicate predicate)
                )
                (TermLike.fullyOverrideSort
                    (termLikeSort term)
                    term
                    -- TODO (virgil): The term sort override above is needed
                    -- because above we're computing the term with (fmap
                    -- unwrapPredicate term) which leaves the original sort at
                    -- the top, while the term's children have sort
                    -- _PREDICATE. We should fix that and not use
                    -- fullyOverrideSort.
                )

{- | Is the 'TermLike' a predicate?

See also: 'makePredicate'

 -}
isPredicate :: InternalVariable variable => TermLike variable -> Bool
isPredicate = Either.isRight . makePredicate

{- | Replace all variables in a @Predicate@ using the provided mapping.
-}
mapVariables
    :: Ord variable1
    => FreshPartialOrd variable2
    => AdjSomeVariableName (variable1 -> variable2)
    -> Predicate variable1
    -> Predicate variable2
mapVariables adj = fmap (TermLike.mapVariables adj)

instance HasFreeVariables (Predicate variable) variable where
    freeVariables = freeVariables . unwrapPredicate

isSimplified :: SideCondition.Representation -> Predicate variable -> Bool
isSimplified sideCondition (GenericPredicate termLike) =
    TermLike.isSimplified sideCondition termLike

simplifiedAttribute :: Predicate variable -> Attribute.Simplified
simplifiedAttribute (GenericPredicate termLike) =
    TermLike.simplifiedAttribute termLike

{- | Mark a 'Predicate' as fully simplified.

The pattern is fully simplified if we do not know how to simplify it any
further. The simplifier reserves the right to skip any pattern which is marked,
so do not mark any pattern unless you are certain it cannot be further
simplified.

-}
markSimplified
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable -> Predicate variable
markSimplified (GenericPredicate termLike) =
    GenericPredicate (TermLike.markSimplified termLike)

markSimplifiedConditional
    :: (HasCallStack, InternalVariable variable)
    => SideCondition.Representation
    -> Predicate variable
    -> Predicate variable
markSimplifiedConditional sideCondition (GenericPredicate termLike) =
    GenericPredicate
        (TermLike.markSimplifiedConditional sideCondition termLike)

markSimplifiedMaybeConditional
    :: (HasCallStack, InternalVariable variable)
    => Maybe SideCondition.Representation
    -> Predicate variable
    -> Predicate variable
markSimplifiedMaybeConditional maybeSideCondition (GenericPredicate termLike) =
    GenericPredicate
        (TermLike.markSimplifiedMaybeConditional maybeSideCondition termLike)

setSimplified
    :: InternalVariable variable
    => Attribute.Simplified -> Predicate variable -> Predicate variable
setSimplified simplified (GenericPredicate termLike) =
    GenericPredicate (TermLike.setSimplified simplified termLike)

forgetSimplified
    :: InternalVariable variable
    => Predicate variable -> Predicate variable
forgetSimplified (GenericPredicate termLike) =
    GenericPredicate (TermLike.forgetSimplified termLike)

-- |Is the predicate free of the given variables?
isFreeOf
    :: Ord variable
    => Predicate variable
    -> Set (SomeVariable variable)
    -> Bool
isFreeOf predicate =
    Set.disjoint (FreeVariables.toSet $ freeVariables predicate)

freeElementVariables :: Predicate variable -> [ElementVariable variable]
freeElementVariables = getFreeElementVariables . freeVariables

hasFreeVariable
    :: Ord variable
    => SomeVariableName variable
    -> Predicate variable
    -> Bool
hasFreeVariable variableName = isFreeVariable variableName . freeVariables

{- | Traverse the predicate from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

 -}
substitute
    :: InternalVariable variable
    => Map (SomeVariableName variable) (TermLike variable)
    -> Predicate variable
    -> Predicate variable
substitute subst (GenericPredicate termLike) =
    GenericPredicate (TermLike.substitute subst termLike)

depth :: Predicate variable -> Int
depth (GenericPredicate predicate) = TermLike.depth predicate
