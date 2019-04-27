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

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate, unwrapPredicate )
import           Kore.Step.Pattern
                 ( Conditional (..), Predicate )
import           Kore.Step.Simplification.Data
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Simplify the 'Synatx.Predicate' once; do not apply the substitution.

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
    => PredicateSimplifier level
    -> StepPatternSimplifier level
    -> Syntax.Predicate variable
    -> BranchT Simplifier (Predicate level variable)
simplifyPartial
    substitutionSimplifier
    termSimplifier
    predicate
  = do
    (patternOr, _proof) <-
        Monad.Trans.lift
        $ simplifyTerm'
        $ Syntax.unwrapPredicate predicate
    -- Despite using Monad.Trans.lift above, we do not need to explicitly check
    -- for \bottom because patternOr is an Or.Pattern.
    scatter (eraseTerm <$> patternOr)
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier
    eraseTerm predicated@Conditional { term }
      | Top_ _ <- term = predicated { term = () }
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse predicated
            ]
