{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
    ( simplifyPredicatesWithSmt
    ) where

import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify, SimplifierVariable )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyPredicate )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
                 ( filterMultiOr )

simplifyPredicatesWithSmt
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => OrPattern variable -> simplifier (OrPattern variable)
simplifyPredicatesWithSmt unsimplified = do
    simplifiedOrs <- traverse
        (BranchT.gather . Pattern.simplifyPredicate)
        (MultiOr.extractPatterns unsimplified)
    SMT.Evaluator.filterMultiOr (MultiOr.make (concat simplifiedOrs))
