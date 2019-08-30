{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
    ( simplifyPredicatesWithSmt
    , filterMultiOrWithTermCeil
    ) where

import           Kore.Internal.Conditional
                 ( Conditional )
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyPredicate )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
                 ( filterMultiOr )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
import           Kore.Variables.Fresh

simplifyPredicatesWithSmt
    ::  ( FreshVariable variable
        , MonadSimplify simplifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => OrPattern variable -> simplifier (OrPattern variable)
simplifyPredicatesWithSmt unsimplified = do
    simplifiedOrs <- traverse
        (BranchT.gather . Pattern.simplifyPredicate)
        (MultiOr.extractPatterns unsimplified)
    filterMultiOrWithTermCeil (MultiOr.make (concat simplifiedOrs))

filterMultiOrWithTermCeil
    :: forall simplifier variable
    .   ( FreshVariable variable
        , MonadSimplify simplifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => OrPattern variable -> simplifier (OrPattern variable)
filterMultiOrWithTermCeil unfiltered = do
    wrapped <- wrapAndAddCeils unfiltered
    filtered <- SMT.Evaluator.filterMultiOr wrapped
    return (fmap unwrap filtered)
  where
    wrapAndAddCeils
        :: OrPattern variable
        -> simplifier (MultiOr (Conditional variable (Pattern variable)))
    wrapAndAddCeils orPattern = do
        orOfOrs <- traverse wrapAndAddCeil orPattern
        return (MultiOr.flatten orOfOrs)
    wrapAndAddCeil
        :: Pattern variable
        -> simplifier (MultiOr (Conditional variable (Pattern variable)))
    wrapAndAddCeil patt = do
        ceils <- Ceil.makeEvaluateTerm predicate term
        return
            (fmap
                (patternWithCondition `Conditional.andCondition`)
                ceils
            )
      where
        (term, predicate) = Pattern.splitTerm patt
        patternWithCondition :: Conditional variable (Pattern variable)
        patternWithCondition = patt `Conditional.withCondition` predicate

    unwrap :: Conditional variable (Pattern variable) -> Pattern variable
    unwrap = Conditional.term
