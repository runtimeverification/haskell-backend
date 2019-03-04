{-|
Module      : Kore.Step.Simplification.Predicate
Description : Predicate simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Predicate
    ( simplifyPartial
    , simplifyPartialBranch
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate, unwrapPredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as Predicated
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Step.Simplification.Data
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Simplifies a predicate, producing another predicate and a substitution,
without trying to reapply the substitution on the predicate.

TODO(virgil): Make this fully simplify.
-}
simplifyPartialBranch
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        )
    => PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> Predicate level variable
    -> BranchT Simplifier (PredicateSubstitution level variable)
simplifyPartialBranch
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        Monad.Trans.lift
        $ simplifier substitutionSimplifier (unwrapPredicate predicate)
    scatter (eraseTerm <$> patternOr)
  where
    eraseTerm predicated
      | Top_ _ <- simplifiedTerm = predicated { term = () }
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse predicated
            ]
      where
        Predicated { term = simplifiedTerm } = predicated

{-| Simplifies a predicate, producing another predicate and a substitution,
without trying to reapply the substitution on the predicate.

TODO(virgil): Make this fully simplify.
-}
simplifyPartial
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        )
    => PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> Predicate level variable
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplifyPartial
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    case MultiOr.extractPatterns patternOr of
        [] -> return
            ( Predicated.bottomPredicate
            , SimplificationProof
            )
        [ predicated ] ->
            return (eraseTerm predicated, SimplificationProof)
        patts ->
            (error . show . Pretty.vsep)
                ( "Expecting at most one result, but found:"
                : (unparse <$> patts)
                )
  where
    eraseTerm predicated
      | Top_ _ <- simplifiedTerm = predicated { term = () }
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse predicated
            ]
      where
        Predicated { term = simplifiedTerm } = predicated
