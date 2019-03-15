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
    ( CommonPredicate -- Constructor not exported on purpose
    , Predicate -- Constructor not exported on purpose
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
    , Kore.Predicate.Predicate.mapVariables
    , stringFromPredicate
    , substitutionToPredicate
    , fromPredicate
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
import           GHC.Generics
                 ( Generic )
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Error
                 ( Error, koreFail )
import           Kore.Step.Pattern
                 ( StepPattern )
import qualified Kore.Step.Pattern as Step.Pattern
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Free
                 ( freePureVariables, pureAllVariables )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| 'GenericPredicate' is a wrapper for predicates used for type safety.
Should not be exported, and should be treated as an opaque entity which
can be manipulated only by functions in this module.
-}
newtype GenericPredicate pat = GenericPredicate pat
    deriving (Eq, Foldable, Functor, Generic, NFData, Ord, Show, Traversable)

instance
    (Hashable pat
    ) => Hashable (GenericPredicate pat)

instance TopBottom patt
    => TopBottom (GenericPredicate patt)
  where
    isTop (GenericPredicate patt) = isTop patt
    isBottom (GenericPredicate patt) = isBottom patt

instance Unparse pattern' => Unparse (GenericPredicate pattern') where
    unparse (GenericPredicate pattern') = unparse pattern'

{-| 'Predicate' is a user-visible representation for predicates.
-}
type Predicate level variable = GenericPredicate (StepPattern level variable)

{-| 'CommonPredicate' follows the generic convention of particularizing types
to Variable.
-}
type CommonPredicate level = Predicate level Variable

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
wrapPredicate :: StepPattern level variable -> Predicate level variable
wrapPredicate = GenericPredicate

{- | Unwrap a 'GenericPredicate'.

This is intended for predicate evaluation and tests and should not be used
outside of that.  We should consider deleting this and implementing the
functionality otherwise.

 -}
unwrapPredicate :: Predicate level variable -> StepPattern level variable
unwrapPredicate (GenericPredicate p) = p

{- | Return the 'StepPattern' corresponding to the given 'Predicate'.

In practice, predicates are flexibly-sorted; the sort argument is used to force
the resulting pattern into a particular sort.

 -}
fromPredicate
    :: ( Unparse (variable level)
       , HasCallStack
       )
    => Sort level  -- ^ Sort of resulting pattern
    -> Predicate level variable
    -> StepPattern level variable
fromPredicate sort (GenericPredicate p) = forceSort sort p

{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate level variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate level variable

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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => [Predicate level variable]
    -> Predicate level variable
makeMultipleAndPredicate =
    foldl' makeAndPredicate makeTruePredicate . nub
    -- 'and' is idempotent so we eliminate duplicates
    -- TODO: This is O(n^2), consider doing something better.

{-| 'makeMultipleOrPredicate' combines a list of Predicates with 'or',
doing some simplification.
-}
makeMultipleOrPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => [Predicate level variable]
    -> Predicate level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Unparse (variable level)
        )
    => Predicate level variable
    -> Predicate level variable
    -> Predicate level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Predicate level variable
    -> Predicate level variable
    -> Predicate level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Predicate level variable
    -> Predicate level variable
    -> Predicate level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Predicate level variable
    -> Predicate level variable
    -> Predicate level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Predicate level variable
    -> Predicate level variable
makeNotPredicate PredicateFalse = makeTruePredicate
makeNotPredicate PredicateTrue  = makeFalsePredicate
makeNotPredicate (GenericPredicate predicate) =
    GenericPredicate $ mkNot predicate

{-| 'makeEqualsPredicate' combines two patterns with equals, producing a
predicate.
-}
makeEqualsPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> StepPattern level variable
    -> Predicate level variable
makeEqualsPredicate first second =
    GenericPredicate $ mkEquals_ first second

{-| 'makeInPredicate' combines two patterns with 'in', producing a
predicate.
-}
makeInPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> StepPattern level variable
    -> Predicate level variable
makeInPredicate first second =
    GenericPredicate $ mkIn_ first second

{-| 'makeCeilPredicate' takes the 'ceil' of a pattern, producing a
predicate.
-}
makeCeilPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> Predicate level variable
makeCeilPredicate patt =
    GenericPredicate $ mkCeil_ patt

{-| 'makeFloorPredicate' takes the 'floor' of a pattern, producing a
predicate.
-}
makeFloorPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> Predicate level variable
makeFloorPredicate patt =
    GenericPredicate $ mkFloor_ patt

{-| Existential quantification for the given variable in the given predicate.
-}
makeExistsPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => variable level
    -> Predicate level variable
    -> Predicate level variable
makeExistsPredicate _ p@PredicateFalse = p
makeExistsPredicate _ t@PredicateTrue = t
makeExistsPredicate v (GenericPredicate p) =
    GenericPredicate $ mkExists v p

{-| Universal quantification for the given variable in the given predicate.
-}
makeForallPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => variable level
    -> Predicate level variable
    -> Predicate level variable
makeForallPredicate _ p@PredicateFalse = p
makeForallPredicate _ t@PredicateTrue = t
makeForallPredicate v (GenericPredicate p) =
    GenericPredicate $ mkForall v p

{-| 'makeTruePredicate' produces a predicate wrapping a 'top'.
-}
makeTruePredicate
    :: MetaOrObject level
    => Predicate level variable
makeTruePredicate = GenericPredicate mkTop_

{-| 'makeFalsePredicate' produces a predicate wrapping a 'bottom'.
-}
makeFalsePredicate
    :: MetaOrObject level
    => Predicate level variable
makeFalsePredicate = GenericPredicate mkBottom_

makePredicate
    :: forall level variable e .
        ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> Either (Error e) (Predicate level variable)
makePredicate = Recursive.elgot makePredicateBottomUp makePredicateTopDown
  where
    makePredicateBottomUp
        :: Base
            (StepPattern level variable)
            (Either (Error e) (Predicate level variable))
        -> Either (Error e) (Predicate level variable)
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
        :: StepPattern level variable
        -> Either
            (Either (Error e) (Predicate level variable))
            (Base (StepPattern level variable) (StepPattern level variable))
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
mapVariables
    :: Ord (to level)
    => (from level -> to level)
    -> Predicate level from
    -> Predicate level to
mapVariables f = fmap (Step.Pattern.mapVariables f)

{- | Extract the set of all (free and bound) variables from a @Predicate@.
-}
allVariables
    :: Ord (variable level)
    => Predicate level variable
    -> Set (variable level)
allVariables = pureAllVariables . unwrapPredicate

{- | Extract the set of free variables from a @Predicate@.
-}
freeVariables
    :: (MetaOrObject level , Ord (variable level))
    => Predicate level variable
    -> Set (variable level)
freeVariables = freePureVariables . unwrapPredicate

{- | 'substitutionToPredicate' transforms a substitution in a predicate.

    An empty substitution list returns a true predicate. A non-empty
    substitution returns a conjunction of variable/substitution equalities.

-}
substitutionToPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Substitution level variable
    -> Predicate level variable
substitutionToPredicate =
    makeMultipleAndPredicate
    . fmap singleSubstitutionToPredicate
    . Substitution.unwrap

singleSubstitutionToPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => (variable level, StepPattern level variable)
    -> Predicate level variable
singleSubstitutionToPredicate (var, patt) =
    makeEqualsPredicate (mkVar var) patt

{- | Traverse the predicate from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

 -}
substitute
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , SortedVariable variable
        )
    => Map (variable level) (StepPattern level variable)
    -> Predicate level variable
    -> Predicate level variable
substitute subst (GenericPredicate stepPattern) =
    GenericPredicate (Step.Pattern.substitute subst stepPattern)
