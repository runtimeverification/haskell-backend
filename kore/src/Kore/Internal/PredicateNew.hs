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

import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Comonad.Trans.Env as Env
import qualified Control.Comonad.Trans.Cofree as Cofree
    (tailF
    )
import Control.DeepSeq
    ( NFData
    )
import qualified Control.Monad.Trans.Reader as Reader
import qualified Data.Bifunctor as Bifunctor
import Data.Containers.ListUtils
    ( nubOrd
    )
import qualified Data.Either as Either
import qualified Data.Foldable as Foldable
import Data.Functor.Const
    ( Const(Const)
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
import qualified Data.Map.Strict as Map
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

import Kore.Attribute.PredicatePattern
    ( PredicatePattern (PredicatePattern)
    )
import qualified Kore.Attribute.Pattern as Attribute.Pattern.DoNotUse
import qualified Kore.Attribute.Pattern as Attribute
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Pattern.Simplified
    ( Simplified(Simplified, NotSimplified)
    )
import Kore.Attribute.Synthetic
import Kore.Variables.Fresh

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
import Kore.Internal.TermLike.Renaming

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
import Kore.Variables.Binding
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
            :: Cofree (PredicateF variable) (PredicatePattern variable)
        }


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

-- Note that we simplify the results of the following 2 functions
-- using nubOrd since we can't get an accurate tree shape anyway
-- because we include 'makeTruePredicate' in the resulting tree
-- (mircea.sebe)
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


newtype NotPredicate variable
    = NotPredicate (TermLikeF variable (Predicate variable))
    deriving (GHC.Generic)

instance SOP.Generic (NotPredicate variable)

instance SOP.HasDatatypeInfo (NotPredicate variable)

instance (Debug (Predicate variable), Debug variable) => Debug (NotPredicate variable)

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
        term <- sequence termE
        predicate <- case (Cofree.tailF term) of
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
        return predicate

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

instance HasFreeVariables (Predicate variable) variable where
    freeVariables (Recursive.project -> attr :< _) = freeVariables attr


isSimplified :: SideCondition.Representation -> Predicate variable -> Bool
isSimplified _ _ = False

simplifiedAttribute :: Predicate variable -> Simplified
simplifiedAttribute _ = NotSimplified


{-
mapVariables
    :: Ord variable1
    => FreshPartialOrd variable2
    => AdjSomeVariableName (variable1 -> variable2)
    -> Predicate variable1
    -> Predicate variable2
mapVariables adj pred = runIdentity (traverseVariables ((.) pure <$> adj) pred)
  where
    traverseVariables
        :: forall variable1 variable2 m
        .  Ord variable1
        => FreshPartialOrd variable2
        => Monad m
        => AdjSomeVariableName (variable1 -> m variable2)
        -> Predicate variable1
        -> m (Predicate variable2)
    traverseVariables adj pred =
        renameFreeVariables adj (freeVariables @_ @variable1 pred)
        >>= Reader.runReaderT (Recursive.fold worker pred)
      where
        adjReader = (.) lift <$> adj
        trElemVar = traverse $ traverseElementVariableName adjReader
        trSetVar = traverse $ traverseSetVariableName adjReader
        traverseExists avoiding =
            existsBinder (renameElementBinder trElemVar avoiding)
        traverseForall avoiding =
            forallBinder (renameElementBinder trElemVar avoiding)
        traverseMu avoiding =
            muBinder (renameSetBinder trSetVar avoiding)
        traverseNu avoiding =
            nuBinder (renameSetBinder trSetVar avoiding)

        worker
            ::  Base
                    (Predicate variable1)
                    (RenamingT variable1 variable2 m (Predicate variable2))
            ->  RenamingT variable1 variable2 m (Predicate variable2)
        worker (attrs :< predF) = do
            attrs' <- Attribute.traverseVariables askSomeVariableName attrs
            let avoiding = freeVariables attrs'
            predF' <- case predF of
                VariableF (Const unifiedVariable) -> do
                    unifiedVariable' <- askSomeVariable unifiedVariable
                    (pure . VariableF) (Const unifiedVariable')
                ExistsF exists -> ExistsF <$> traverseExists avoiding exists
                ForallF forall -> ForallF <$> traverseForall avoiding forall
                MuF mu -> MuF <$> traverseMu avoiding mu
                NuF nu -> NuF <$> traverseNu avoiding nu
                _ ->
                    sequence termLikeF >>=
                    -- traverseVariablesF will not actually call the traversals
                    -- because all the cases with variables are handled above.
                    traverseVariablesF askSomeVariableName
            (pure . Recursive.embed) (attrs' :< termLikeF')
-}


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
substitute subst pred =
        substituteNone <|> substituteBinder <|> substituteTermLike
        & fromMaybe substituteDefault
  where
    freeVars = FreeVariables.toNames (freeVariables pred)
    subst' = Map.intersection subst (Map.fromSet id freeVars)
    originalVariables = Set.difference freeVars (Map.keysSet subst')
    targetFreeVariables = Foldable.foldl' Set.union Set.empty
        (FreeVariables.toNames <$> freeVariables <$> subst')
    freeVariables' = Set.union originalVariables targetFreeVariables
    avoidCapture = refreshElementVariable freeVariables'

    substituteNone
        | Map.null subst' = pure pred
        | otherwise       = empty

    substituteBinder = case predF of
        ExistsF (exists'@(Exists {existsVariable = var, existsChild = child})) -> do
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
        ForallF (forall'@(Forall {forallVariable = var, forallChild = child})) -> do
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
        _ :< predF = Recursive.project pred

    substituteTermLike = case predF of
        CeilF (ceil'@(Ceil {ceilChild})) ->
            pure $ synthesize $ CeilF $ ceil'
            { ceilChild = TermLike.substitute subst' ceilChild
            }
        EqualsF (equals'@(Equals {equalsFirst, equalsSecond})) ->
            pure $ synthesize $ EqualsF $ equals'
            { equalsFirst  = TermLike.substitute subst' equalsFirst
            , equalsSecond = TermLike.substitute subst' equalsSecond
            }
        FloorF (floor'@(Floor {floorChild})) ->
            pure $ synthesize $ FloorF $ floor'
            { floorChild = TermLike.substitute subst' floorChild
            }
        InF (in'@(In {inContainedChild, inContainingChild})) ->
            pure $ synthesize $ InF $ in'
            { inContainedChild  = TermLike.substitute subst' inContainedChild
            , inContainingChild = TermLike.substitute subst' inContainingChild
            }
        _ -> empty
      where
        _ :< predF = Recursive.project pred

    substituteDefault = synthesize (substitute subst' <$> predF)
      where
        _ :< predF = Recursive.project pred

depth :: Predicate variable -> Int
depth = Recursive.fold levelDepth
  where
    levelDepth (_ :< predF) = 1 + foldl' max 0 predF
