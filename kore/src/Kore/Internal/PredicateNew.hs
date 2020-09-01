{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.PredicateNew
    ( Predicate -- Constructor not exported on purpose
    {- , pattern PredicateAnd
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
    , Kore.Internal.PredicateNew.forgetSimplified
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
    , substitute -}
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Env as Env
import qualified Control.Comonad.Trans.Cofree as Cofree
    (tailF
    )
import Control.DeepSeq
    ( NFData
    )
import qualified Data.Bifunctor as Bifunctor
import Data.Containers.ListUtils
    ( nubOrd
    )
import qualified Data.Either as Either
import qualified Data.Foldable as Foldable
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.List
    ( foldl'
    )
import Data.Map.Strict
    ( Map
    )
import Data.Set
    ( Set
    )

import Data.Functor.Compose
    ( Compose (..)
    )
import Data.Functor.Identity
    ( Identity (..)
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.PredicatePattern as Attribute
    ( PredicatePattern (PredicatePattern)
    )
import qualified Kore.Attribute.Pattern as Attribute.Pattern.DoNotUse
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Synthetic

import Kore.Debug
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike hiding
    ( AndF
    , BottomF
    , CeilF
    , EqualsF
    , ExistsF
    , FloorF
    , ForallF
    , IffF
    , ImpliesF
    , InF
    , NotF
    , OrF
    , TopF
    , depth
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

import Kore.Syntax.And
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Not
import Kore.Syntax.Or
import Kore.Syntax.Top

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


data PredicateF variable child
    = AndF           !(And () child)
    | BottomF        !(Bottom () child)
    | CeilF          !(Ceil () (TermLike variable))
    | EqualsF        !(Equals () (TermLike variable))
    | ExistsF        !(Exists () variable child)
    | FloorF         !(Floor () (TermLike variable))
    | ForallF        !(Forall () variable child)
    | IffF           !(Iff () child)
    | ImpliesF       !(Implies () child)
    | InF            !(In () (TermLike variable))
    | NotF           !(Not () child)
    | OrF            !(Or () child)
    | TopF           !(Top () child)
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)


instance
    Ord variable => Synthetic (FreeVariables variable) (PredicateF variable)
  where
    synthetic =
        \case
            AndF and' -> synthetic and'
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic (freeVariables <$> ceil)
            EqualsF equals -> synthetic (freeVariables <$> equals)
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic (freeVariables <$> floor')
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic (freeVariables <$> in')
            NotF not' -> synthetic not'
            OrF or' -> synthetic or'
            TopF top -> synthetic top


newtype Predicate variable =
    Predicate
        { getPredicate
            :: Cofree (PredicateF variable) (Attribute.PredicatePattern variable)
        }


type instance Base (Predicate variable) =
    CofreeF (PredicateF variable) (Attribute.PredicatePattern variable)


-- This instance implements all class functions for the TermLike newtype
-- because the their implementations for the inner type may be specialized.
instance Recursive (Predicate variable) where
    project = \(Predicate embedded) ->
        case Recursive.project embedded of
            Compose (Identity projected) -> Predicate <$> projected
    {-# INLINE project #-}

    -- This specialization is particularly important: The default implementation
    -- of 'cata' in terms of 'project' would involve an extra call to 'fmap' at
    -- every level of the tree due to the implementation of 'project' above.
    cata alg = \(Predicate fixed) ->
        Recursive.cata
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE cata #-}

    para alg = \(Predicate fixed) ->
        Recursive.para
            (\(Compose (Identity base)) ->
                 alg (Bifunctor.first Predicate <$> base)
            )
            fixed
    {-# INLINE para #-}

    gpara dist alg = \(Predicate fixed) ->
        Recursive.gpara
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> alg (Env.local Predicate <$> base))
            fixed
    {-# INLINE gpara #-}

    prepro pre alg = \(Predicate fixed) ->
        Recursive.prepro
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE prepro #-}

    gprepro dist pre alg = \(Predicate fixed) ->
        Recursive.gprepro
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE gprepro #-}

-- This instance implements all class functions for the Predicate newtype
-- because the their implementations for the inner type may be specialized.
instance Corecursive (Predicate variable) where
    embed = \projected ->
        (Predicate . Recursive.embed . Compose . Identity)
            (getPredicate <$> projected)
    {-# INLINE embed #-}

    ana coalg = Predicate . ana0
      where
        ana0 =
            Recursive.ana (Compose . Identity . coalg)
    {-# INLINE ana #-}

    apo coalg = Predicate . apo0
      where
        apo0 =
            Recursive.apo
                (\a ->
                     (Compose . Identity)
                        (Bifunctor.first getPredicate <$> coalg a)
                )
    {-# INLINE apo #-}

    postpro post coalg = Predicate . postpro0
      where
        postpro0 =
            Recursive.postpro
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE postpro #-}

    gpostpro dist post coalg = Predicate . gpostpro0
      where
        gpostpro0 =
            Recursive.gpostpro
                (Compose . Identity . dist . (<$>) (runIdentity . getCompose))
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE gpostpro #-}



{- | Return the 'TermLike' corresponding to the given 'Predicate'. -}
fromPredicate
    :: (InternalVariable variable, HasCallStack)
    => Sort  -- ^ Sort of resulting pattern
    -> Predicate variable
    -> TermLike variable
fromPredicate sort =
    Recursive.fold $ synthesize . (\case
        AndF      x -> TermLike.AndF x {andSort = sort}
        BottomF   x -> TermLike.BottomF x {bottomSort = sort}
        CeilF     x -> TermLike.CeilF x {ceilOperandSort = sort, ceilResultSort = sort}
        EqualsF   x -> TermLike.EqualsF x {equalsOperandSort = sort, equalsResultSort = sort}
        ExistsF   x -> TermLike.ExistsF x {existsSort = sort}
        FloorF    x -> TermLike.FloorF x {floorOperandSort = sort, floorResultSort = sort}
        ForallF   x -> TermLike.ForallF x {forallSort = sort}
        IffF      x -> TermLike.IffF x {iffSort = sort}
        ImpliesF  x -> TermLike.ImpliesF x {impliesSort = sort}
        InF       x -> TermLike.InF x {inOperandSort = sort, inResultSort = sort}
        NotF      x -> TermLike.NotF x {notSort = sort}
        OrF       x -> TermLike.OrF x {orSort = sort}
        TopF      x -> TermLike.TopF x {topSort = sort}
    ) . Cofree.tailF


{-|'PredicateFalse' is a pattern for matching 'bottom' predicates.
-}
pattern PredicateFalse :: Predicate variable

{-|'PredicateTrue' is a pattern for matching 'top' predicates.
-}
pattern PredicateTrue :: Predicate variable

pattern PredicateFalse <- (Recursive.project -> _ :< BottomF _)
pattern PredicateTrue  <- (Recursive.project -> _ :< TopF _)

pattern PredicateAnd
    :: Predicate variable -> Predicate variable -> Predicate variable
pattern PredicateAnd p1 p2 <- (Recursive.project -> _ :< AndF And {andSort = (), andFirst = p1, andSecond = p2})

pattern PredicateOr
    :: Predicate variable -> Predicate variable -> Predicate variable
pattern PredicateOr p1 p2 <- (Recursive.project -> _ :< OrF Or {orSort = (), orFirst = p1, orSecond = p2})

{-|'isFalse' checks whether a predicate is obviously bottom.
-}
isFalse :: TopBottom patt => patt -> Bool
isFalse = isBottom

isTrue :: TopBottom patt => patt -> Bool
isTrue = not . isBottom

makeTruePredicate :: InternalVariable variable => Predicate variable
makeTruePredicate = synthesize (TopF Top {topSort = ()})

makeFalsePredicate :: InternalVariable variable => Predicate variable
makeFalsePredicate = synthesize $ BottomF Bottom {bottomSort = ()}

{-| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
-}
makeNotPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
makeNotPredicate p = synthesize $ NotF Not
    { notSort = ()
    , notChild = p
    }

makeAndPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeAndPredicate p1 p2 = synthesize $ AndF And
    { andSort = ()
    , andFirst = p1
    , andSecond = p2
    }

makeOrPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeOrPredicate p1 p2 = synthesize $ OrF Or
    { orSort = ()
    , orFirst = p1
    , orSecond = p2
    }

makeImpliesPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeImpliesPredicate p1 p2 = synthesize $ ImpliesF Implies
    { impliesSort = ()
    , impliesFirst = p1
    , impliesSecond = p2
    }

makeIffPredicate
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeIffPredicate p1 p2 = synthesize $ IffF Iff
    { iffSort = ()
    , iffFirst = p1
    , iffSecond = p2
    }

makeCeilPredicate
    :: (HasCallStack, InternalVariable variable)
    => TermLike variable
    -> Predicate variable
makeCeilPredicate t = synthesize $ CeilF Ceil
    { ceilOperandSort = ()
    , ceilResultSort = ()
    , ceilChild = t
    }

makeFloorPredicate
    :: (HasCallStack, InternalVariable variable)
    => TermLike variable
    -> Predicate variable
makeFloorPredicate t = synthesize $ FloorF Floor
    { floorOperandSort = ()
    , floorResultSort = ()
    , floorChild = t
    }

makeInPredicate
    :: (HasCallStack, InternalVariable variable)
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate t1 t2 = synthesize $ InF In
    { inOperandSort = ()
    , inResultSort = ()
    , inContainedChild = t1
    , inContainingChild = t2
    }

makeEqualsPredicate
    :: (HasCallStack, InternalVariable variable)
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate t1 t2 = synthesize $ EqualsF Equals
    { equalsOperandSort = ()
    , equalsResultSort = ()
    , equalsFirst = t1
    , equalsSecond = t2
    }

makeExistsPredicate
    :: (HasCallStack, InternalVariable variable)
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeExistsPredicate v p = synthesize $ ExistsF Exists
    { existsSort = ()
    , existsVariable = v
    , existsChild = p
    }

makeForallPredicate
    :: (HasCallStack, InternalVariable variable)
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeForallPredicate v p = synthesize $ ForallF Forall
    { forallSort = ()
    , forallVariable = v
    , forallChild = p
    }

makeMultipleAndPredicate
    :: (InternalVariable variable, Ord (Predicate variable))
    => [Predicate variable]
    -> Predicate variable
makeMultipleAndPredicate =
    foldl' makeAndPredicate makeTruePredicate . nubOrd
    -- 'and' is idempotent so we eliminate duplicates

makeMultipleOrPredicate
    :: (InternalVariable variable, Ord (Predicate variable))
    => [Predicate variable]
    -> Predicate variable
makeMultipleOrPredicate =
    foldl' makeOrPredicate makeFalsePredicate . nubOrd
    -- 'or' is idempotent so we eliminate duplicates

makeMultipleExists
    :: (Foldable f, InternalVariable variable)
    => f (ElementVariable variable)
    -> Predicate variable
    -> Predicate variable
makeMultipleExists vars p =
    foldr makeExistsPredicate p vars

makeMultipleForalls
    :: (Foldable f, InternalVariable variable)
    => f (ElementVariable variable)
    -> Predicate variable
    -> Predicate variable
makeMultipleForalls vars p =
    foldr makeForallPredicate p vars

getMultiAndPredicate
    :: Predicate variable
    -> [Predicate variable]
getMultiAndPredicate = \case
    PredicateAnd p1 p2 -> concatMap getMultiAndPredicate [p1, p2]
    p -> [p]

getMultiOrPredicate
    :: Predicate variable
    -> [Predicate variable]
getMultiOrPredicate = \case
    PredicateOr p1 p2 -> concatMap getMultiOrPredicate [p1, p2]
    p -> [p]

{-
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
-}

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

instance SOP.Generic (NotPredicate variable)

instance SOP.HasDatatypeInfo (NotPredicate variable)

instance Debug variable => Debug (NotPredicate variable)

instance InternalVariable variable => Pretty (NotPredicate variable) where
    pretty (NotPredicate termLikeF) =
        Pretty.vsep
        [ "Expected a predicate, but found:"
        , Pretty.indent 4 (unparse termLikeF)
        ]