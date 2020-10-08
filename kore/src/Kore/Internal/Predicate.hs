{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Predicate
    ( Predicate -- Constructor not exported on purpose
    , PredicateF
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
        )
    , fromPredicate
    , fromPredicate_
    , makePredicate
    , isFalse
    , isTrue
    , makeTruePredicate
    , makeFalsePredicate
    , makeNotPredicate
    , makeAndPredicate
    , makeOrPredicate
    , makeImpliesPredicate
    , makeIffPredicate
    , makeCeilPredicate
    , makeFloorPredicate
    , makeInPredicate
    , makeEqualsPredicate
    , makeExistsPredicate
    , makeForallPredicate
    , makeMultipleAndPredicate
    , makeMultipleOrPredicate
    , makeMultipleExists
    , makeMultipleForalls
    , getMultiAndPredicate
    , getMultiOrPredicate
    , NotPredicate
    , isPredicate
    , simplifiedAttribute
    , isSimplified
    , isFreeOf
    , freeElementVariables
    , hasFreeVariable
    , traverseVariablesF
    , mapVariables
    , substitute
    , depth
    , markSimplified
    , markSimplifiedConditional
    , markSimplifiedMaybeConditional
    , setSimplified
    , forgetSimplified
    , wrapPredicate
    , pattern PredicateTrue
    , pattern PredicateFalse
    , pattern PredicateAnd
    , pattern PredicateOr
    , pattern PredicateNot
    , pattern PredicateCeil
    , pattern PredicateFloor
    , pattern PredicateEquals
    , pattern PredicateIn
    , pattern PredicateExists
    , pattern PredicateForall
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Env as Env
import Control.DeepSeq
    ( NFData (rnf)
    )
import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Monad.Trans.Reader as Reader
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Either as Either
import qualified Data.Foldable as Foldable
import Data.Functor.Const
    ( Const (Const)
    )
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
import qualified Data.Map.Strict as Map
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

import Kore.Attribute.Pattern.FreeVariables as FreeVariables
    ( FreeVariables
    , HasFreeVariables (..)
    , getFreeElementVariables
    , isFreeVariable
    , toNames
    , toSet
    )
import Kore.Attribute.Pattern.Simplified
    ( Simplified (NotSimplified)
    )
import qualified Kore.Attribute.Pattern.Simplified as Simplified
import Kore.Attribute.PredicatePattern
    ( PredicatePattern
    )
import qualified Kore.Attribute.PredicatePattern as Attribute
import Kore.Attribute.Synthetic
import Kore.Variables.Fresh
    ( refreshElementVariable
    )

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
    , extractAttributes
    , forgetSimplified
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
import Kore.Internal.TermLike.Renaming
import Kore.Sort
    ( predicateSort
    )

import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
import Kore.Variables.Binding
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

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
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    (Ord variable, Unparse variable, Unparse child) => Unparse (PredicateF variable child)
  where
    unparse = unparseGeneric
    unparse2 = unparse2Generic

instance
    Ord variable => Synthetic (FreeVariables variable) (PredicateF variable)
  where
    synthetic = \case
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

instance Synthetic Simplified (PredicateF variable)
  where
    synthetic = \case
        AndF and' -> synthetic and'
        BottomF bottom -> synthetic bottom
        CeilF ceil -> synthetic (TermLike.simplifiedAttribute <$> ceil)
        EqualsF equals -> synthetic (TermLike.simplifiedAttribute <$> equals)
        ExistsF exists -> synthetic exists
        FloorF floor' -> synthetic (TermLike.simplifiedAttribute <$> floor')
        ForallF forall' -> synthetic forall'
        IffF iff -> synthetic iff
        ImpliesF implies -> synthetic implies
        InF in' -> synthetic (TermLike.simplifiedAttribute <$> in')
        NotF not' -> synthetic not'
        OrF or' -> synthetic or'
        TopF top -> synthetic top


newtype Predicate variable =
    Predicate
        { getPredicate
            :: Cofree (PredicateF variable) (PredicatePattern variable)
        }
    deriving (GHC.Generic, Show)

instance SOP.Generic (Predicate variable)

instance SOP.HasDatatypeInfo (Predicate variable)

instance Debug variable => Debug (Predicate variable)

instance (Debug variable, Diff variable) => Diff (Predicate variable) where
    diffPrec
        pred1@(Recursive.project -> attrs1 :< predF1)
        pred2@(Recursive.project -> _      :< predF2)
      =
        -- If the patterns differ, do not display the difference in the
        -- attributes, which would overload the user with redundant information.
        diffPrecGeneric
            (Recursive.embed (attrs1 :< predF1))
            (Recursive.embed (attrs1 :< predF2))
        <|> diffPrecGeneric pred1 pred2

instance
    (Eq variable, Eq (PredicateF variable (Predicate variable)))
    => Eq (Predicate variable)
  where
    (==)
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2)
      = pat1 == pat2

instance
    (Ord variable, Ord (PredicateF variable (Predicate variable)))
    => Ord (Predicate variable)
  where
    compare
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2)
      = compare pat1 pat2

instance Hashable variable => Hashable (Predicate variable) where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance NFData variable => NFData (Predicate variable) where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat

instance (Unparse variable, Ord variable) => Unparse (Predicate variable) where
    unparse term =
        case Recursive.project term of
            (attrs :< predF) -> Pretty.sep [attributeRepresentation, unparse predF]
              where
                attributeRepresentation = Pretty.surround
                            (Pretty.hsep $ map Pretty.pretty representation)
                            "/* "
                            " */"
                  where
                    representation =
                        case
                            Simplified.unparseTag
                            (Attribute.simplifiedAttribute attrs)
                        of
                            Just result -> [result]
                            Nothing -> []

    unparse2 term =
        case Recursive.project term of
          (_ :< pat) -> unparse2 pat

instance Unparse (Predicate variable) => SQL.Column (Predicate variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

type instance Base (Predicate variable) =
    CofreeF (PredicateF variable) (PredicatePattern variable)


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

instance TopBottom (Predicate variable) where
    isTop PredicateTrue = True
    isTop _ = False
    isBottom PredicateFalse = True
    isBottom _ = False

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
pattern PredicateAnd p1 p2 <-
    (Recursive.project -> _ :< AndF (And () p1 p2))

pattern PredicateOr
    :: Predicate variable -> Predicate variable -> Predicate variable
pattern PredicateOr p1 p2 <-
    (Recursive.project -> _ :< OrF (Or () p1 p2))

pattern PredicateNot :: Predicate variable -> Predicate variable
pattern PredicateNot p <-
    (Recursive.project -> _ :< NotF (Not () p))

pattern PredicateCeil :: TermLike variable -> Predicate variable
pattern PredicateCeil t <- (Recursive.project -> _ :< CeilF (Ceil () () t))

pattern PredicateFloor :: TermLike variable -> Predicate variable
pattern PredicateFloor t <- (Recursive.project -> _ :< FloorF (Floor () () t))

pattern PredicateEquals :: TermLike variable -> TermLike variable -> Predicate variable
pattern PredicateEquals t1 t2 <- (Recursive.project -> _ :< EqualsF (Equals () () t1 t2))

pattern PredicateIn :: TermLike variable -> TermLike variable -> Predicate variable
pattern PredicateIn t1 t2 <- (Recursive.project -> _ :< InF (In () () t1 t2))

pattern PredicateExists :: ElementVariable variable -> Predicate variable -> Predicate variable
pattern PredicateExists var p <- (Recursive.project -> _ :< ExistsF (Exists () var p))

pattern PredicateForall :: ElementVariable variable -> Predicate variable -> Predicate variable
pattern PredicateForall var p <- (Recursive.project -> _ :< ForallF (Forall () var p))


{- | Return the 'TermLike' corresponding to the given 'Predicate'. -}
fromPredicate
    :: InternalVariable variable
    => Sort
    -- ^ Sort of resulting pattern
    -> Predicate variable
    -> TermLike variable
fromPredicate sort =
    Recursive.fold $ \case
        _ :< AndF     (And () t1 t2)       -> TermLike.mkAnd t1 t2
        _ :< BottomF  _                    -> TermLike.mkBottom sort
        _ :< CeilF    (Ceil () () t)       -> TermLike.mkCeil sort t
        _ :< EqualsF  (Equals () () t1 t2) -> TermLike.mkEquals sort t1 t2
        _ :< ExistsF  (Exists () v t)      -> TermLike.mkExists v t
        _ :< FloorF   (Floor () () t)      -> TermLike.mkFloor sort t
        _ :< ForallF  (Forall () v t)      -> TermLike.mkForall v t
        _ :< IffF     (Iff () t1 t2)       -> TermLike.mkIff t1 t2
        _ :< ImpliesF (Implies () t1 t2)   -> TermLike.mkImplies t1 t2
        _ :< InF      (In () () t1 t2)     -> TermLike.mkIn sort t1 t2
        _ :< NotF     (Not () t)           -> TermLike.mkNot t
        _ :< OrF      (Or () t1 t2)        -> TermLike.mkOr t1 t2
        _ :< TopF      _                   -> TermLike.mkTop sort

fromPredicate_
    :: InternalVariable variable
    => Predicate variable
    -> TermLike variable
fromPredicate_ = fromPredicate predicateSort

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

makeNotPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
makeNotPredicate p = synthesize $ NotF Not
    { notSort = ()
    , notChild = p
    }

{-| 'makeAndPredicate' combines two Predicates with an 'and', doing some
simplification.
-}
makeAndPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeAndPredicate p1 p2 = synthesize $ AndF And
    { andSort = ()
    , andFirst = p1
    , andSecond = p2
    }

makeOrPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeOrPredicate p1 p2 = synthesize $ OrF Or
    { orSort = ()
    , orFirst = p1
    , orSecond = p2
    }

makeImpliesPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeImpliesPredicate p1 p2 = synthesize $ ImpliesF Implies
    { impliesSort = ()
    , impliesFirst = p1
    , impliesSecond = p2
    }

makeIffPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
    -> Predicate variable
makeIffPredicate p1 p2 = synthesize $ IffF Iff
    { iffSort = ()
    , iffFirst = p1
    , iffSecond = p2
    }

makeCeilPredicate
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeCeilPredicate t = synthesize $ CeilF Ceil
    { ceilOperandSort = ()
    , ceilResultSort = ()
    , ceilChild = t
    }

makeFloorPredicate
    :: InternalVariable variable
    => TermLike variable
    -> Predicate variable
makeFloorPredicate t = synthesize $ FloorF Floor
    { floorOperandSort = ()
    , floorResultSort = ()
    , floorChild = t
    }

makeInPredicate
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeInPredicate = TermLike.makeSortsAgree makeInWorker
  where
    makeInWorker t1 t2 _ = synthesize $ InF $ In () () t1 t2

makeEqualsPredicate
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
makeEqualsPredicate = TermLike.makeSortsAgree makeEqualsWorker
  where
    makeEqualsWorker t1 t2 _ = synthesize $ EqualsF $ Equals () () t1 t2

makeExistsPredicate
    :: InternalVariable variable
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeExistsPredicate v p = synthesize $ ExistsF Exists
    { existsSort = ()
    , existsVariable = v
    , existsChild = p
    }

makeForallPredicate
    :: InternalVariable variable
    => ElementVariable variable
    -> Predicate variable
    -> Predicate variable
makeForallPredicate v p = synthesize $ ForallF Forall
    { forallSort = ()
    , forallVariable = v
    , forallChild = p
    }

makeMultipleAndPredicate
    :: InternalVariable variable
    => [Predicate variable]
    -> Predicate variable
makeMultipleAndPredicate [] = makeTruePredicate
makeMultipleAndPredicate (p : ps) = foldl' makeAndPredicate p ps

makeMultipleOrPredicate
    :: InternalVariable variable
    => [Predicate variable]
    -> Predicate variable
makeMultipleOrPredicate [] = makeFalsePredicate
makeMultipleOrPredicate (p : ps) = foldl' makeOrPredicate p ps

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


newtype NotPredicate variable
    = NotPredicate (TermLikeF variable (Predicate variable))
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance (Unparse (Predicate variable), InternalVariable variable) => Pretty (NotPredicate variable) where
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
makePredicate = Recursive.elgot makePredicateBottomUp makePredicateTopDown
  where
    makePredicateBottomUp
        :: Base
            (TermLike variable)
            (Either (NotPredicate variable) (Predicate variable))
        -> Either (NotPredicate variable) (Predicate variable)
    makePredicateBottomUp termE = do
        _ :< term <- sequence termE
        case term of
            TermLike.TopF _ -> return makeTruePredicate
            TermLike.BottomF _ -> return makeFalsePredicate
            TermLike.AndF p -> return $ makeAndPredicate (andFirst p) (andSecond p)
            TermLike.OrF p -> return $ makeOrPredicate (orFirst p) (orSecond p)
            TermLike.IffF p -> return $ makeIffPredicate (iffFirst p) (iffSecond p)
            TermLike.ImpliesF p -> return $
                makeImpliesPredicate (impliesFirst p) (impliesSecond p)
            TermLike.NotF p -> return $ makeNotPredicate (notChild p)
            TermLike.ExistsF p -> return $
                makeExistsPredicate (existsVariable p) (existsChild p)
            TermLike.ForallF p -> return $
                makeForallPredicate (forallVariable p) (forallChild p)
            p -> Left (NotPredicate p)

    makePredicateTopDown
        :: TermLike variable
        -> Either
            (Either (NotPredicate variable) (Predicate variable))
            (Base (TermLike variable) (TermLike variable))
    makePredicateTopDown (Recursive.project -> projected@(_ :< pat)) =
        case pat of
            TermLike.CeilF Ceil { ceilChild } ->
                (Left . pure) (makeCeilPredicate ceilChild)
            TermLike.FloorF Floor { floorChild } ->
                (Left . pure) (makeFloorPredicate floorChild)
            TermLike.EqualsF Equals { equalsFirst, equalsSecond } ->
                (Left . pure) (makeEqualsPredicate equalsFirst equalsSecond)
            TermLike.InF In { inContainedChild, inContainingChild } ->
                (Left . pure) (makeInPredicate inContainedChild inContainingChild)
            _ -> Right projected

isPredicate :: InternalVariable variable => TermLike variable -> Bool
isPredicate = Either.isRight . makePredicate

extractAttributes :: Predicate variable -> PredicatePattern variable
extractAttributes (Recursive.project -> attr :< _) = attr

instance HasFreeVariables (Predicate variable) variable where
    freeVariables = freeVariables . extractAttributes

simplifiedAttribute :: Predicate variable -> Simplified
simplifiedAttribute = Attribute.simplifiedAttribute . extractAttributes

isSimplified :: SideCondition.Representation -> Predicate variable -> Bool
isSimplified condition = Attribute.isSimplified condition . extractAttributes

cannotSimplifyNotSimplifiedError
    :: (HasCallStack, InternalVariable variable)
    => PredicateF variable (Predicate variable) -> a
cannotSimplifyNotSimplifiedError predF =
    error
        (  "Unexpectedly marking term with NotSimplified children as \
            \simplified:\n"
        ++ show predF
        ++ "\n"
        ++ unparseToString predF
        )

simplifiedFromChildren
    :: HasCallStack
    => PredicateF variable (Predicate variable) -> Simplified
simplifiedFromChildren predF =
    case mergedSimplified of
        NotSimplified -> NotSimplified
        _ -> mergedSimplified `Simplified.simplifiedTo` Simplified.fullySimplified
  where
    mergedSimplified = foldMap simplifiedAttribute predF

checkedSimplifiedFromChildren
    :: (HasCallStack, InternalVariable variable)
    => PredicateF variable (Predicate variable) -> Simplified
checkedSimplifiedFromChildren predF =
    case simplifiedFromChildren predF of
        NotSimplified -> cannotSimplifyNotSimplifiedError predF
        simplified -> simplified

markSimplified
    :: (HasCallStack, InternalVariable variable)
    => Predicate variable -> Predicate variable
markSimplified (Recursive.project -> attrs :< predF) =
    Recursive.embed
        (  Attribute.setSimplified
            (checkedSimplifiedFromChildren predF)
            attrs
        :< predF
        )

markSimplifiedConditional
    :: (HasCallStack, InternalVariable variable)
    => SideCondition.Representation -> Predicate variable -> Predicate variable
markSimplifiedConditional
    condition
    (Recursive.project -> attrs :< predF)
  =
    Recursive.embed
        (  Attribute.setSimplified
                (  checkedSimplifiedFromChildren predF
                <> Simplified.simplifiedConditionally condition
                )
                attrs
        :< predF
        )

markSimplifiedMaybeConditional
    :: (HasCallStack, InternalVariable variable)
    => Maybe SideCondition.Representation
    -> Predicate variable
    -> Predicate variable
markSimplifiedMaybeConditional Nothing = markSimplified
markSimplifiedMaybeConditional (Just condition) =
    markSimplifiedConditional condition

setSimplified
    :: (HasCallStack, InternalVariable variable)
    => Simplified -> Predicate variable -> Predicate variable
setSimplified
    simplified
    (Recursive.project -> attrs :< predF)
  =
    Recursive.embed
        (  Attribute.setSimplified mergedSimplified attrs
        :< predF
        )
  where
    childSimplified = simplifiedFromChildren predF
    mergedSimplified = case (childSimplified, simplified) of
        (NotSimplified, NotSimplified) -> NotSimplified
        (NotSimplified, _) -> cannotSimplifyNotSimplifiedError predF
        (_, NotSimplified) -> NotSimplified
        _ -> childSimplified <> simplified

forgetSimplified
    :: InternalVariable variable
    => Predicate variable
    -> Predicate variable
forgetSimplified = resynthesize

traverseVariablesF
    :: ( Ord variable1
       , FreshPartialOrd variable2
       , Monad f
       )
    => AdjSomeVariableName (variable1 -> f variable2)
    -> PredicateF variable1 child
    -> f (PredicateF variable2 child)
traverseVariablesF adj =
    \case
        ExistsF any0 -> ExistsF <$> traverseVariablesExists any0
        ForallF all0 -> ForallF <$> traverseVariablesForall all0
        AndF andP -> pure (AndF andP)
        BottomF botP -> pure (BottomF botP)
        CeilF ceilP -> do
            termLike <- sequence (TermLike.traverseVariables adj <$> ceilP)
            return $ CeilF termLike
        EqualsF eqP -> do
            termLike <- sequence (TermLike.traverseVariables adj <$> eqP)
            return $ EqualsF termLike
        FloorF flrP -> do
            termLike <- sequence (TermLike.traverseVariables adj <$> flrP)
            return $ FloorF termLike
        IffF iffP -> pure (IffF iffP)
        ImpliesF impP -> pure (ImpliesF impP)
        InF inP -> do
            termLike <- sequence (TermLike.traverseVariables adj <$> inP)
            return $ InF termLike
        NotF notP -> pure (NotF notP)
        OrF orP -> pure (OrF orP)
        TopF topP -> pure (TopF topP)
  where
    trElemVar = traverse $ traverseElementVariableName adj
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort
        <$> trElemVar existsVariable
        <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort
        <$> trElemVar forallVariable
        <*> pure forallChild

mapVariables
    :: forall variable1 variable2
    . Ord variable1
    => FreshPartialOrd variable2
    => AdjSomeVariableName (variable1 -> variable2)
    -> Predicate variable1
    -> Predicate variable2
mapVariables (fmap ((.) pure) -> adj) predicate = runIdentity $
    renameFreeVariables adj (freeVariables @_ @variable1 predicate)
    >>= Reader.runReaderT (Recursive.fold worker predicate)
  where
    adjReader :: AdjSomeVariableName
        (variable1
        -> ReaderT
            (VariableNameMap variable1 variable2) Identity variable2)
    adjReader = (.) lift <$> adj
    trElemVar = traverse $ traverseElementVariableName adjReader
    traverseExists avoiding =
        existsBinder (renameElementBinder trElemVar avoiding)
    traverseForall avoiding =
        forallBinder (renameElementBinder trElemVar avoiding)

    worker
        ::  Base
                (Predicate variable1)
                (RenamingT variable1 variable2 Identity (Predicate variable2))
        ->  RenamingT variable1 variable2 Identity (Predicate variable2)
    worker (attrs :< predF) = do
        attrs' <- Attribute.traverseVariables askSomeVariableName attrs
        let avoiding = freeVariables attrs'
        predF' <- case predF of
            ExistsF exists -> ExistsF <$> traverseExists avoiding exists
            ForallF forall -> ForallF <$> traverseForall avoiding forall
            _ -> sequence predF >>= traverseVariablesF askSomeVariableName
        (pure . Recursive.embed) (attrs' :< predF')

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



 -- !!  The following is just a temporary solution and      !!
 -- !!  the code using wrapPredicate should be refactored   !!

wrapPredicate ::
    InternalVariable variable
    => TermLike variable -> Predicate variable
wrapPredicate = either
    (error "Term cannot be wrapped.\n\
            \Input TermLike is not a Predicate \
            \despite being supposed to be\n"
    )
    id
    . makePredicate

substitute
    :: InternalVariable variable
    => Map (SomeVariableName variable) (TermLike variable)
    -> Predicate variable
    -> Predicate variable
substitute subst predicate =
        substituteNone <|> substituteBinder <|> substituteTermLike
        & fromMaybe substituteDefault
  where
    freeVars = FreeVariables.toNames (freeVariables predicate)
    subst' = Map.intersection subst (Map.fromSet id freeVars)
    originalVariables = Set.difference freeVars (Map.keysSet subst')
    targetFreeVariables = Foldable.foldl' Set.union Set.empty
        (FreeVariables.toNames . freeVariables <$> subst')
    freeVariables' = Set.union originalVariables targetFreeVariables
    avoidCapture = refreshElementVariable freeVariables'

    substituteNone
        | Map.null subst' = pure predicate
        | otherwise       = empty

    substituteBinder = case predF of
        ExistsF exists'@Exists {existsVariable = var, existsChild = child} -> do
            newVar <- avoidCapture var
            return $ synthesize $ ExistsF $ exists'
                { existsVariable = newVar
                , existsChild = substitute
                    (Map.insert
                        (inject (variableName var))
                        (synthesize $ TermLike.VariableF $ Const $ mkSomeVariable newVar)
                        subst'
                    )
                    child
                }
        ForallF forall'@Forall {forallVariable = var, forallChild = child} -> do
            newVar <- avoidCapture var
            return $ synthesize $ ForallF $ forall'
                { forallVariable = newVar
                , forallChild = substitute
                    (Map.insert
                        (inject (variableName var))
                        (synthesize $ TermLike.VariableF $ Const $ mkSomeVariable newVar)
                        subst'
                    )
                    child
                }
        _ -> empty
      where
        _ :< predF = Recursive.project predicate

    substituteTermLike = case predF of
        CeilF ceil'@Ceil {ceilChild} ->
            pure $ synthesize $ CeilF $ ceil'
            { ceilChild = TermLike.substitute subst' ceilChild
            }
        EqualsF equals'@Equals {equalsFirst, equalsSecond} ->
            pure $ synthesize $ EqualsF $ equals'
            { equalsFirst  = TermLike.substitute subst' equalsFirst
            , equalsSecond = TermLike.substitute subst' equalsSecond
            }
        FloorF floor'@Floor {floorChild} ->
            pure $ synthesize $ FloorF $ floor'
            { floorChild = TermLike.substitute subst' floorChild
            }
        InF in'@In {inContainedChild, inContainingChild} ->
            pure $ synthesize $ InF $ in'
            { inContainedChild  = TermLike.substitute subst' inContainedChild
            , inContainingChild = TermLike.substitute subst' inContainingChild
            }
        _ -> empty
      where
        _ :< predF = Recursive.project predicate

    substituteDefault = synthesize (substitute subst' <$> predF)
      where
        _ :< predF = Recursive.project predicate

depth :: Predicate variable -> Int
depth = Recursive.fold levelDepth
  where
    levelDepth (_ :< predF) = 1 + foldl' max 0 predF
