{-|
Module      : Kore.Predicate.Predicate
Description : Data structure holding a predicate and basic tools like
              predicate constructors.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Predicate.Predicate
    ( Predicate -- Constructor not exported on purpose
    , pattern PredicateFalse
    , pattern PredicateTrue
    , compactPredicatePredicate
    , isFalse
    , makePredicate
    , isPredicate
    , makeAndPredicate
    , makeMultipleAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeExistsPredicate
    , makeMultipleExists
    , makeForallPredicate
    , makeFalsePredicate
    , makeFloorPredicate
    , makeIffPredicate
    , makeImpliesPredicate
    , makeInPredicate
    , makeMuPredicate
    , makeNotPredicate
    , makeNuPredicate
    , makeOrPredicate
    , makeMultipleOrPredicate
    , makeTruePredicate
    , isSimplified
    , markSimplified
    , freeVariables
    , isFreeOf
    , Kore.Predicate.Predicate.freeElementVariables
    , Kore.Predicate.Predicate.hasFreeVariable
    , Kore.Predicate.Predicate.mapVariables
    , singleSubstitutionToPredicate
    , stringFromPredicate
    , coerceSort
    , fromPredicate
    , fromSubstitution
    , unwrapPredicate
    , wrapPredicate
    , Kore.Predicate.Predicate.substitute
    ) where

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Either as Either
import Data.Functor.Foldable
    ( Base
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Hashable
import Data.List
    ( foldl'
    , nub
    )
import Data.Map.Strict
    ( Map
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import GHC.Stack
    ( HasCallStack
    )

import Kore.Attribute.Pattern.FreeVariables
import Kore.Debug
import Kore.Error
    ( Error
    , koreFail
    )
import Kore.Internal.TermLike hiding
    ( freeVariables
    , isSimplified
    , markSimplified
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (GenericPredicate pat)

instance SOP.HasDatatypeInfo (GenericPredicate pat)

instance Debug pat => Debug (GenericPredicate pat)

instance (Debug pat, Diff pat) => Diff (GenericPredicate pat)

instance Hashable pat => Hashable (GenericPredicate pat)

instance NFData pat => NFData (GenericPredicate pat)

instance TopBottom patt => TopBottom (GenericPredicate patt) where
    isTop (GenericPredicate patt) = isTop patt
    isBottom (GenericPredicate patt) = isBottom patt

instance
    (Ord variable, SortedVariable variable)
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
    :: (SortedVariable variable, Unparse variable, HasCallStack)
    => Sort  -- ^ Sort of resulting pattern
    -> Predicate variable
    -> TermLike variable
fromPredicate sort (GenericPredicate p) = TermLike.forceSort sort p

{- | Change a 'Predicate' from one 'Sort' to another.

This is a safe operation because predicates are flexibly sorted.

 -}
coerceSort
    :: (SortedVariable variable, Unparse variable)
    => Sort
    -> Predicate variable
    -> Predicate variable
coerceSort sort = fmap (TermLike.forceSort sort)

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate variable

pattern PredicateFalse <- GenericPredicate (Recursive.project -> _ :< BottomF _)
pattern PredicateTrue  <- GenericPredicate (Recursive.project -> _ :< TopF _)

{-|'isFalse' checks whether a predicate is obviously bottom.
-}
isFalse :: TopBottom patt => GenericPredicate patt -> Bool
isFalse = isBottom

{-| 'makeMultipleAndPredicate' combines a list of Predicates with 'and',
doing some simplification.
-}
makeMultipleAndPredicate
    :: InternalVariable variable
    => [Predicate variable]
    -> Predicate variable
makeMultipleAndPredicate =
    foldl' makeAndPredicate makeTruePredicate . nub
    -- 'and' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

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
    foldl' makeOrPredicate makeFalsePredicate . nub
    -- 'or' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

{-| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
-}
makeAndPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeAndPredicate b@PredicateFalse _ = b
makeAndPredicate _ b@PredicateFalse = b
makeAndPredicate PredicateTrue second = second
makeAndPredicate first PredicateTrue = first
makeAndPredicate p@(GenericPredicate first) (GenericPredicate second)
  | first == second = p
  | otherwise =
    GenericPredicate (TermLike.mkAnd first second)

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
makeOrPredicate p@(GenericPredicate first) (GenericPredicate second)
  | first == second = p
  | otherwise =
    GenericPredicate (TermLike.mkOr first second)

{-| 'makeImpliesPredicate' combines two Predicates into an
implication, doing some simplification.
-}
makeImpliesPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeImpliesPredicate PredicateFalse _ = makeTruePredicate
makeImpliesPredicate _ t@PredicateTrue = t
makeImpliesPredicate PredicateTrue second = second
makeImpliesPredicate first PredicateFalse = makeNotPredicate first
makeImpliesPredicate (GenericPredicate first) (GenericPredicate second) =
    GenericPredicate $ TermLike.mkImplies first second

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
makeIffPredicate (GenericPredicate first) (GenericPredicate second) =
    GenericPredicate $ TermLike.mkIff first second

{-| 'makeNotPredicate' negates an evaluated Predicate, doing some
simplification.
-}
makeNotPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
makeNotPredicate PredicateFalse = makeTruePredicate
makeNotPredicate PredicateTrue  = makeFalsePredicate
makeNotPredicate (GenericPredicate predicate) =
    GenericPredicate $ TermLike.mkNot predicate

{-| 'makeEqualsPredicate' combines two patterns with equals, producing a
predicate.
-}
makeEqualsPredicate
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate first second =
    GenericPredicate $ TermLike.mkEquals_ first second

{-| 'makeInPredicate' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate first second =
    GenericPredicate $ TermLike.mkIn_ first second

{-| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeCeilPredicate patt =
    GenericPredicate $ TermLike.mkCeil_ patt

{-| 'makeFloorPredicate' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeFloorPredicate patt =
    GenericPredicate $ TermLike.mkFloor_ patt

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

{-| 'makeTruePredicate' produces a predicate wrapping a 'top'.
-}
makeTruePredicate :: InternalVariable variable => Predicate variable
makeTruePredicate = GenericPredicate TermLike.mkTop_

{-| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate :: InternalVariable variable => Predicate variable
makeFalsePredicate = GenericPredicate TermLike.mkBottom_

makePredicate
    :: forall variable e
    .  InternalVariable variable
    => TermLike variable
    -> Either (Error e) (Predicate variable)
makePredicate = Recursive.elgot makePredicateBottomUp makePredicateTopDown
  where
    makePredicateBottomUp
        :: Base
            (TermLike variable)
            (Either (Error e) (Predicate variable))
        -> Either (Error e) (Predicate variable)
    makePredicateBottomUp (_ :< patE) = do
        pat <- sequence patE
        case pat of
            TopF _ -> return makeTruePredicate
            BottomF _ -> return makeFalsePredicate
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
            p -> koreFail
                ("Cannot translate to predicate: " ++ show p)
    makePredicateTopDown
        :: TermLike variable
        -> Either
            (Either (Error e) (Predicate variable))
            (Base (TermLike variable) (TermLike variable))
    makePredicateTopDown (Recursive.project -> projected@(_ :< pat)) =
        case pat of
            CeilF Ceil { ceilChild } ->
                (Left . pure) (makeCeilPredicate ceilChild)
            FloorF Floor { floorChild } ->
                (Left . pure) (makeFloorPredicate floorChild)
            EqualsF Equals { equalsFirst, equalsSecond } ->
                (Left . pure) (makeEqualsPredicate equalsFirst equalsSecond)
            InF In { inContainedChild, inContainingChild } ->
                (Left . pure)
                    (makeInPredicate inContainedChild inContainingChild)
            _ -> Right projected

{- | Is the 'TermLike' a predicate?

See also: 'makePredicate'

 -}
isPredicate :: InternalVariable variable => TermLike variable -> Bool
isPredicate = Either.isRight . makePredicate

{- | Replace all variables in a @Predicate@ using the provided mapping.
-}
mapVariables :: Ord to => (from -> to) -> Predicate from -> Predicate to
mapVariables f = fmap (TermLike.mapVariables f)

{- | Extract the set of free variables from a @Predicate@.
-}
freeVariables
    :: Ord variable
    => Predicate variable
    -> FreeVariables variable
freeVariables = TermLike.freeVariables . unwrapPredicate

isSimplified :: Predicate variable -> Bool
isSimplified (GenericPredicate termLike) = TermLike.isSimplified termLike

{- | Mark a 'Predicate' as fully simplified.

The pattern is fully simplified if we do not know how to simplify it any
further. The simplifier reserves the right to skip any pattern which is marked,
so do not mark any pattern unless you are certain it cannot be further
simplified.

 -}
markSimplified :: Predicate variable -> Predicate variable
markSimplified (GenericPredicate termLike) =
    GenericPredicate (TermLike.markSimplified termLike)

isFreeOf
    :: Ord variable
    => Predicate variable
    -> Set (UnifiedVariable variable)
    -> Bool
isFreeOf predicate =
    Set.disjoint (getFreeVariables $ freeVariables predicate)

freeElementVariables
    :: Ord variable
    => Predicate variable
    -> [ElementVariable variable]
freeElementVariables =
    getFreeElementVariables . Kore.Predicate.Predicate.freeVariables

hasFreeVariable
    :: Ord variable
    => UnifiedVariable variable
    -> Predicate variable
    -> Bool
hasFreeVariable variable =
    isFreeVariable variable . Kore.Predicate.Predicate.freeVariables

singleSubstitutionToPredicate
    :: InternalVariable variable
    => (UnifiedVariable variable, TermLike variable)
    -> Predicate variable
singleSubstitutionToPredicate (var, patt) =
    -- markSimplified because this should only be called when we don't know what
    -- to do with a substitution.
    markSimplified $ makeEqualsPredicate (TermLike.mkVar var) patt

{- | @fromSubstitution@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
fromSubstitution
    :: InternalVariable variable
    => Substitution variable
    -> Predicate variable
fromSubstitution =
    makeMultipleAndPredicate
    . fmap singleSubstitutionToPredicate
    . Substitution.unwrap

{- | Traverse the predicate from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

 -}
substitute
    :: SubstitutionVariable variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Predicate variable
    -> Predicate variable
substitute subst (GenericPredicate termLike) =
    GenericPredicate (TermLike.substitute subst termLike)
