{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

-- For instance Applicative:
{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.SideCondition
    ( SideCondition  -- Constructor not exported on purpose
    , fromCondition
    , fromPredicate
    , andCondition
    , assumeTrueCondition
    , assumeTruePredicate
    , mapVariables
    , top
    , topTODO
    , toPredicate
    , toRepresentation
    , replaceTerm
    , cannotReplace
    , simplifyConjunctionByAssumption
    , emptyReplacements
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Control.Monad.State.Strict
    ( StateT
    , runStateT
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Functor.Foldable as Recursive
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( sortOn
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Changed
import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Internal.Symbol
    ( isConstructor
    , isFunction
    )
import Kore.Internal.TermLike
    ( pattern App_
    , pattern Builtin_
    , pattern Equals_
    , pattern Exists_
    , pattern Forall_
    , pattern Inj_
    , pattern InternalBool_
    , pattern InternalBytes_
    , pattern InternalInt_
    , pattern InternalString_
    , pattern Mu_
    , pattern Not_
    , pattern Nu_
    , TermLike
    , mkBottom
    , mkTop
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Syntax.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import Pair
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

{-| Side condition used in the evaluation context.

It is not added to the result.

It is usually used to remove infeasible branches, but it may also be used for
other purposes, say, to remove redundant parts of the result predicate.
-}
data SideCondition variable =
    SideCondition
        { assumedTrue :: MultiAnd (Predicate variable)
        , replacements :: HashMap (TermLike variable) (TermLike variable)
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => SQL.Column (SideCondition variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

instance TopBottom (SideCondition variable) where
    isTop sideCondition@(SideCondition _ _) =
        isTop assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition
    isBottom sideCondition@(SideCondition _ _) =
        isBottom assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition

instance Ord variable => HasFreeVariables (SideCondition variable) variable
  where
    freeVariables sideCondition@(SideCondition _ _) =
        freeVariables assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition

instance InternalVariable variable => Unparse (SideCondition variable) where
    unparse = unparse . toPredicate
    unparse2 = unparse2 . toPredicate

instance InternalVariable variable => Pretty (SideCondition variable) where
    pretty SideCondition { assumedTrue, replacements } =
        Pretty.vsep $
            [ "Assumed true condition:"
            , Pretty.indent 4 (unparse . MultiAnd.toPredicate $ assumedTrue)
            , "Replacements:"
            ]
            <> fmap (\(k, v) -> Pretty.lparen <> unparse k <> Pretty.comma <> unparse v <> Pretty.rparen) (HashMap.toList replacements)

instance From (SideCondition variable) (MultiAnd (Predicate variable))
  where
    from condition@(SideCondition _ _) = assumedTrue condition
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (MultiAnd (Predicate variable)) (SideCondition variable)
  where
    from multiAnd =
        let (assumedTrue, replacements) =
                  simplifyConjunctionByAssumption multiAnd
                  & extract
         in SideCondition { assumedTrue, replacements }
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (SideCondition variable) (Predicate variable)
  where
    from = toPredicate
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (Predicate variable) (SideCondition variable)
  where
    from = fromPredicate
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (Condition variable) (SideCondition variable)
  where
    from = fromCondition
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (SideCondition variable) (Condition variable)
  where
    from = Condition.fromPredicate . toPredicate
    {-# INLINE from #-}

top :: InternalVariable variable => SideCondition variable
top = SideCondition { assumedTrue = MultiAnd.top, replacements = mempty }

-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => SideCondition variable
topTODO = top

andCondition
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
andCondition
    sideCondition
    (from @(Condition _) @(MultiAnd _) -> newCondition)
  =
    let combinedConditions = oldCondition <> newCondition
        (assumedTrue, replacements) =
            simplifyConjunctionByAssumption combinedConditions
            & extract
     in SideCondition { assumedTrue, replacements }
  where
    SideCondition { assumedTrue = oldCondition } = sideCondition

assumeTrueCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
assumeTrueCondition = fromCondition

assumeTruePredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
assumeTruePredicate = fromPredicate

toPredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
toPredicate condition@(SideCondition _ _) =
    MultiAnd.toPredicate assumedTrue
  where
    SideCondition { assumedTrue } = condition

fromPredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
fromPredicate = from @(MultiAnd _) . MultiAnd.fromPredicate

-- TODO: docs
emptyReplacements
    :: InternalVariable variable
    => SideCondition variable
    -> SideCondition variable
emptyReplacements sideCondition =
    sideCondition { replacements = mempty }

mapVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> SideCondition variable1
    -> SideCondition variable2
mapVariables adj condition@(SideCondition _ _) =
    let assumedTrue' =
            MultiAnd.map (Predicate.mapVariables adj) assumedTrue
        replacements' =
            mapKeysAndValues (TermLike.mapVariables adj) replacements
     in SideCondition
            { assumedTrue = assumedTrue'
            , replacements = replacements'
            }
  where
    SideCondition { assumedTrue, replacements } = condition
    mapKeysAndValues f hashMap =
        HashMap.fromList
        $ Bifunctor.bimap f f
        <$> HashMap.toList hashMap

fromCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
fromCondition = fromPredicate . Condition.toPredicate

toRepresentation
    :: InternalVariable variable
    => SideCondition variable
    -> SideCondition.Representation
toRepresentation =
    mkRepresentation
    . mapVariables @_ @VariableName (pure toVariableName)

-- TODO: docs
replaceTerm
    :: InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> TermLike variable
replaceTerm SideCondition { replacements } original =
    HashMap.findWithDefault original original replacements

cannotReplace
    :: InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Bool
cannotReplace SideCondition { replacements } term =
    HashMap.lookup term replacements & isNothing

{- | Simplify the conjunction of 'Predicate' clauses by assuming each is true.
The conjunction is simplified by the identity:
@
A ∧ P(A) = A ∧ P(⊤)
@
 -}
simplifyConjunctionByAssumption
    :: forall variable
    .  InternalVariable variable
    => MultiAnd (Predicate variable)
    -> Changed
        ( MultiAnd (Predicate variable)
        , HashMap (TermLike variable) (TermLike variable)
        )
simplifyConjunctionByAssumption (toList -> andPredicates) =
    (fmap . Bifunctor.first) MultiAnd.make
    $ flip runStateT HashMap.empty
    $ for (sortBySize andPredicates)
    $ \predicate' -> do
        let original = Predicate.unwrapPredicate predicate'
        result <- applyAssumptions original
        assume result
        return result
  where
    -- Sorting by size ensures that every clause is considered before any clause
    -- which could contain it, because the containing clause is necessarily
    -- larger.
    sortBySize :: [Predicate variable] -> [Predicate variable]
    sortBySize = sortOn (size . from)

    size :: TermLike variable -> Int
    size =
        Recursive.fold $ \(_ :< termLikeF) ->
            case termLikeF of
                TermLike.EvaluatedF evaluated -> TermLike.getEvaluated evaluated
                TermLike.DefinedF defined -> TermLike.getDefined defined
                _ -> 1 + sum termLikeF

    assume
        :: Predicate variable
        -> StateT (HashMap (TermLike variable) (TermLike variable)) Changed ()
    assume predicate1 =
        State.modify' (assumeEqualTerms . assumePredicate)
      where
        assumePredicate =
            case termLike of
                Not_ _ notChild ->
                    -- Infer that the predicate is \bottom.
                    HashMap.insert notChild (mkBottom sort)
                _ ->
                    -- Infer that the predicate is \top.
                    HashMap.insert termLike (mkTop sort)
        assumeEqualTerms =
            case retractLocalFunction termLike of
                Just (Pair term1 term2) -> HashMap.insert term1 term2
                _ -> id

        termLike = Predicate.unwrapPredicate predicate1
        sort = termLikeSort termLike

    applyAssumptions
        ::  TermLike variable
        ->  StateT (HashMap (TermLike variable) (TermLike variable)) Changed
                (Predicate variable)
    applyAssumptions replaceIn = do
        assumptions <- State.get
        lift $ fmap
            (unsafeMakePredicate assumptions replaceIn)
            (applyAssumptionsWorker assumptions replaceIn)

    unsafeMakePredicate replacements original result =
        case Predicate.makePredicate result of
            -- TODO (ttuegel): https://github.com/kframework/kore/issues/1442
            -- should make it impossible to have an error here.
            Left err ->
                (error . show . Pretty.vsep . map (either id (Pretty.indent 4)))
                [ Left "Replacing"
                , Right (Pretty.vsep (unparse <$> HashMap.keys replacements))
                , Left "in"
                , Right (unparse original)
                , Right (Pretty.pretty err)
                ]
            Right p -> p

    applyAssumptionsWorker
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> Changed (TermLike variable)
    applyAssumptionsWorker assumptions original
      | Just result <- HashMap.lookup original assumptions = Changed result

      | HashMap.null assumptions' = Unchanged original

      | otherwise =
        traverse (applyAssumptionsWorker assumptions') replaceIn
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | Exists_ _ var _ <- original = restrictAssumptions (inject var)
          | Forall_ _ var _ <- original = restrictAssumptions (inject var)
          | Mu_       var _ <- original = restrictAssumptions (inject var)
          | Nu_       var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            HashMap.filterWithKey
                (\termLike _ -> wouldNotCapture termLike)
                assumptions
          where
            wouldNotCapture = not . TermLike.hasFreeVariable variableName

{- | Get a local function definition from a 'TermLike'.
A local function definition is a predicate that we can use to evaluate a
function locally (based on the side conditions) when none of the functions
global definitions (axioms) apply. We are looking for a 'TermLike' of the form
@
\equals(f(...), C(...))
@
where @f@ is a function and @C@ is a constructor, sort injection or builtin.
@retractLocalFunction@ will match an @\equals@ predicate with its arguments
in either order, but the function pattern is always returned first in the
'Pair'.
 -}
retractLocalFunction
    :: TermLike variable
    -> Maybe (Pair (TermLike variable))
retractLocalFunction =
    \case
        Equals_ _ _ term1 term2 -> go term1 term2 <|> go term2 term1
        _ -> Nothing
  where
    go term1@(App_ symbol1 _) term2
      | isFunction symbol1 =
        -- TODO (thomas.tuegel): Add tests.
        case term2 of
            App_ symbol2 _
              | isConstructor symbol2 -> Just (Pair term1 term2)
            Inj_ _     -> Just (Pair term1 term2)
            Builtin_ _ -> Just (Pair term1 term2)
            InternalInt_ _ -> Just (Pair term1 term2)
            InternalBytes_ _ _ -> Just (Pair term1 term2)
            InternalString_ _ -> Just (Pair term1 term2)
            InternalBool_ _ -> Just (Pair term1 term2)
            _          -> Nothing
    go _ _ = Nothing
