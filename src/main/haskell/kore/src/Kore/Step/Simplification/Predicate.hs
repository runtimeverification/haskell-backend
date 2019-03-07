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
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Predicate.Predicate
       ( Predicate, unwrapPredicate )
import Kore.Step.Representation.ExpandedPattern
       ( PredicateSubstitution, Predicated (..) )
import Kore.Step.Simplification.Data
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

{- | Simplify the 'Predicate' once; return but do not apply the substitution.

@simplifyPartial@ does not attempt to apply the resulting substitution and
re-simplify the result; see "Kore.Step.Simplification.PredicateSubstitution".

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
    -> BranchT Simplifier (PredicateSubstitution level variable)
simplifyPartial
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        Monad.Trans.lift
        $ simplifier substitutionSimplifier (unwrapPredicate predicate)
    scatter (eraseTerm <$> patternOr)
  where
    eraseTerm predicated@Predicated { term }
      | Top_ _ <- term = predicated { term = () }
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse predicated
            ]
