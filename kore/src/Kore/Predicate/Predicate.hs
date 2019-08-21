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
    , freeVariables
    , isFreeOf
    , Kore.Predicate.Predicate.freeElementVariables
    , Kore.Predicate.Predicate.hasFreeVariable
    , Kore.Predicate.Predicate.mapVariables
    , stringFromPredicate
    , substitutionToPredicate
    , fromPredicate
    , fromSubstitution
    , unwrapPredicate
    , wrapPredicate
    , Kore.Predicate.Predicate.substitute
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Hashable
import           Data.List
                 ( foldl', nub )
import           Data.Map.Strict
                 ( Map )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Attribute.Pattern.FreeVariables
import           Kore.Debug
import           Kore.Error
                 ( Error, koreFail )
import           Kore.Internal.TermLike hiding
                 ( freeVariables )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (GenericPredicate pat)

instance SOP.HasDatatypeInfo (GenericPredicate pat)

instance Debug pat => Debug (GenericPredicate pat)

instance Hashable pat => Hashable (GenericPredicate pat)

instance NFData pat => NFData (GenericPredicate pat)

instance TopBottom patt => TopBottom (GenericPredicate patt) where
    isTop (GenericPredicate patt) = isTop patt
    isBottom (GenericPredicate patt) = isBottom patt

instance Unparse pattern' => Unparse (GenericPredicate pattern') where
    unparse (GenericPredicate pattern') = unparse pattern'
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => [Predicate variable]
    -> Predicate variable
makeMultipleAndPredicate =
    foldl' makeAndPredicate makeTruePredicate . nub
    -- 'and' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

{-| 'makeMultipleOrPredicate' combines a list of Predicates with 'or',
doing some simplification.
-}
makeMultipleOrPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate first second =
    GenericPredicate $ TermLike.mkEquals_ first second

{-| 'makeInPredicate' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate first second =
    GenericPredicate $ TermLike.mkIn_ first second

{-| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate
    ::  ( Ord variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> Predicate variable
makeCeilPredicate patt =
    GenericPredicate $ TermLike.mkCeil_ patt

{-| 'makeFloorPredicate' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate
    ::  ( Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => TermLike variable
    -> Predicate variable
makeFloorPredicate patt =
    GenericPredicate $ TermLike.mkFloor_ patt

{-| Existential quantification for the given variable in the given predicate.
-}
makeExistsPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( Foldable f
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => f (ElementVariable variable)
    -> Predicate variable
    -> Predicate variable
makeMultipleExists vars phi =
    foldr makeExistsPredicate phi vars

{-| Universal quantification for the given variable in the given predicate.
-}
makeForallPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SetVariable variable
    -> Predicate variable
    -> Predicate variable
makeNuPredicate _ p@PredicateFalse = p
makeNuPredicate _ t@PredicateTrue = t
makeNuPredicate v (GenericPredicate p) =
    GenericPredicate $ TermLike.mkNu v p

{-| 'makeTruePredicate' produces a predicate wrapping a 'top'.
-}
makeTruePredicate
    :: (Ord variable, SortedVariable variable) => Predicate variable
makeTruePredicate = GenericPredicate TermLike.mkTop_

{-| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate
    :: (Ord variable, SortedVariable variable) => Predicate variable
makeFalsePredicate = GenericPredicate TermLike.mkBottom_

makePredicate
    :: forall variable e.
        ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
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

{- | 'substitutionToPredicate' transforms a substitution in a predicate.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable/substitution equalities.

-}
substitutionToPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Substitution variable
    -> Predicate variable
substitutionToPredicate =
    makeMultipleAndPredicate
    . fmap singleSubstitutionToPredicate
    . Substitution.unwrap

singleSubstitutionToPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => (UnifiedVariable variable, TermLike variable)
    -> Predicate variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (TermLike.mkVar var) patt

{- | @fromSubstitution@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
fromSubstitution
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Substitution variable
    -> Predicate variable
fromSubstitution = substitutionToPredicate

{- | Traverse the predicate from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

 -}
substitute
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        )
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Predicate variable
    -> Predicate variable
substitute subst (GenericPredicate termLike) =
    GenericPredicate (TermLike.substitute subst termLike)
