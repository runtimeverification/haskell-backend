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
    , makeNotPredicate
    , makeOrPredicate
    , makeMultipleOrPredicate
    , makeTruePredicate
    , allVariables
    , Kore.Predicate.Predicate.freeVariables
    , hasFreeVariable
    , Kore.Predicate.Predicate.mapVariables
    , stringFromPredicate
    , substitutionToPredicate
    , fromPredicate
    , fromSubstitution
    , unwrapPredicate
    , wrapPredicate
    , substitute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Data.Functor.Foldable as Recursive
import           Data.Hashable
import           Data.List
                 ( foldl', nub )
import           Data.Map.Strict
                 ( Map )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Error
                 ( Error, koreFail )
import           Kore.Step.TermLike
                 ( TermLike )
import qualified Kore.Step.TermLike as TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Free
                 ( pureAllVariables )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Foldable, Functor, Generic, NFData, Ord, Show, Traversable)

instance Hashable pat => Hashable (GenericPredicate pat)

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
    :: ( Unparse variable
       , HasCallStack
       )
    => Sort  -- ^ Sort of resulting pattern
    -> Predicate variable
    -> TermLike variable
fromPredicate sort (GenericPredicate p) = forceSort sort p

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate variable

pattern PredicateFalse
    <- GenericPredicate (Recursive.project -> _ :< BottomPattern _)
pattern PredicateTrue
    <- GenericPredicate (Recursive.project -> _ :< TopPattern _)

{-|'isFalse' checks whether a predicate is obviously bottom.
-}
isFalse :: TopBottom patt => GenericPredicate patt -> Bool
isFalse = isBottom

{-| 'makeMultipleAndPredicate' combines a list of Predicates with 'and',
doing some simplification.
-}
makeMultipleAndPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    -- TODO(virgil): Group these constraints in a class
    -- or, even better, a type (like ShowMetaOrObject in MetaOrObject).
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    GenericPredicate (mkAnd first second)

{-| 'makeOrPredicate' combines two Predicates with an 'or', doing
some simplification.
-}
makeOrPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    GenericPredicate (mkOr first second)

{-| 'makeImpliesPredicate' combines two Predicates into an
implication, doing some simplification.
-}
makeImpliesPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    GenericPredicate $ mkImplies first second

{-| 'makeIffPredicate' combines two evaluated with an 'iff', doing
some simplification.
-}
makeIffPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    GenericPredicate $ mkIff first second

{-| 'makeNotPredicate' negates an evaluated Predicate, doing some
simplification.
-}
makeNotPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Eq variable
        , Show variable
        , Unparse variable
        )
    => Predicate variable
    -> Predicate variable
makeNotPredicate PredicateFalse = makeTruePredicate
makeNotPredicate PredicateTrue  = makeFalsePredicate
makeNotPredicate (GenericPredicate predicate) =
    GenericPredicate $ mkNot predicate

{-| 'makeEqualsPredicate' combines two patterns with equals, producing a
predicate.
-}
makeEqualsPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate first second =
    GenericPredicate $ mkEquals_ first second

{-| 'makeInPredicate' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate first second =
    GenericPredicate $ mkIn_ first second

{-| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> Predicate variable
makeCeilPredicate patt =
    GenericPredicate $ mkCeil_ patt

{-| 'makeFloorPredicate' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> Predicate variable
makeFloorPredicate patt =
    GenericPredicate $ mkFloor_ patt

{-| Existential quantification for the given variable in the given predicate.
-}
makeExistsPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => variable
    -> Predicate variable
    -> Predicate variable
makeExistsPredicate _ p@PredicateFalse = p
makeExistsPredicate _ t@PredicateTrue = t
makeExistsPredicate v (GenericPredicate p) =
    GenericPredicate $ mkExists v p

{- | Existentially-quantify the given variables over the predicate.
 -}
makeMultipleExists
    ::  ( Foldable f
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => f variable
    -> Predicate variable
    -> Predicate variable
makeMultipleExists vars phi =
    foldr makeExistsPredicate phi vars

{-| Universal quantification for the given variable in the given predicate.
-}
makeForallPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => variable
    -> Predicate variable
    -> Predicate variable
makeForallPredicate _ p@PredicateFalse = p
makeForallPredicate _ t@PredicateTrue = t
makeForallPredicate v (GenericPredicate p) =
    GenericPredicate $ mkForall v p

{-| 'makeTruePredicate' produces a predicate wrapping a 'top'.
-}
makeTruePredicate
    :: MetaOrObject Object
    => Predicate variable
makeTruePredicate = GenericPredicate mkTop_

{-| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate
    :: MetaOrObject Object
    => Predicate variable
makeFalsePredicate = GenericPredicate mkBottom_

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
            TopPattern _ -> return makeTruePredicate
            BottomPattern _ -> return makeFalsePredicate
            AndPattern p -> return $ makeAndPredicate (andFirst p) (andSecond p)
            OrPattern p -> return $ makeOrPredicate (orFirst p) (orSecond p)
            IffPattern p -> return $ makeIffPredicate (iffFirst p) (iffSecond p)
            ImpliesPattern p -> return $
                makeImpliesPredicate (impliesFirst p) (impliesSecond p)
            NotPattern p -> return $ makeNotPredicate (notChild p)
            ExistsPattern p -> return $
                makeExistsPredicate (existsVariable p) (existsChild p)
            ForallPattern p -> return $
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
            CeilPattern Ceil { ceilChild } ->
                (Left . pure) (makeCeilPredicate ceilChild)
            FloorPattern Floor { floorChild } ->
                (Left . pure) (makeFloorPredicate floorChild)
            EqualsPattern Equals { equalsFirst, equalsSecond } ->
                (Left . pure) (makeEqualsPredicate equalsFirst equalsSecond)
            InPattern In { inContainedChild, inContainingChild } ->
                (Left . pure)
                    (makeInPredicate inContainedChild inContainingChild)
            _ -> Right projected

{- | Replace all variables in a @Predicate@ using the provided mapping.
-}
mapVariables :: Ord to => (from -> to) -> Predicate from -> Predicate to
mapVariables f = fmap (TermLike.mapVariables f)

{- | Extract the set of all (free and bound) variables from a @Predicate@.
-}
allVariables
    :: Ord variable
    => Predicate variable
    -> Set variable
allVariables = pureAllVariables . unwrapPredicate

{- | Extract the set of free variables from a @Predicate@.
-}
freeVariables
    :: (MetaOrObject Object , Ord variable)
    => Predicate variable
    -> Set variable
freeVariables = TermLike.freeVariables . unwrapPredicate

hasFreeVariable
    :: Ord variable
    => variable
    -> Predicate variable
    -> Bool
hasFreeVariable variable =
    Set.member variable . Kore.Predicate.Predicate.freeVariables

{- | 'substitutionToPredicate' transforms a substitution in a predicate.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable/substitution equalities.

-}
substitutionToPredicate
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => (variable, TermLike variable)
    -> Predicate variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (mkVar var) patt

{- | @fromSubstitution@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
fromSubstitution
    ::  ( MetaOrObject Object
        , SortedVariable variable
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
        , MetaOrObject Object
        , Ord variable
        , SortedVariable variable
        )
    => Map variable (TermLike variable)
    -> Predicate variable
    -> Predicate variable
substitute subst (GenericPredicate termLike) =
    GenericPredicate (TermLike.substitute subst termLike)
