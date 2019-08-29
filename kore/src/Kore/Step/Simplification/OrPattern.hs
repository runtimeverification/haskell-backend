{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
  ( simplifyPredicatesWithSmt
    )
where

import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
  ( OrPattern
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
  ( filterMultiOr
    )
import Kore.Step.Simplification.Data
  ( MonadSimplify
    )
import qualified Kore.Step.Simplification.Data as BranchT
  ( gather
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
  ( simplifyPredicate
    )
import Kore.Syntax.Variable
  ( SortedVariable
    )
import Kore.Unparser
import Kore.Variables.Fresh

simplifyPredicatesWithSmt
  :: ( FreshVariable variable,
       MonadSimplify simplifier,
       Ord variable,
       Show variable,
       SortedVariable variable,
       Unparse variable
       )
  => OrPattern variable
  -> simplifier (OrPattern variable)
simplifyPredicatesWithSmt unsimplified = do
  simplifiedOrs <-
    traverse
      (BranchT.gather . Pattern.simplifyPredicate)
      (MultiOr.extractPatterns unsimplified)
  SMT.Evaluator.filterMultiOr (MultiOr.make (concat simplifiedOrs))
