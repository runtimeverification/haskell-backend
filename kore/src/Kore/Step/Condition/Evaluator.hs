{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( simplify
    ) where

import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data
                 ( MonadSimplify, simplifyTerm )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Attempt to simplify a predicate. -}
simplify
    ::  forall variable m .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , MonadSimplify m
        )
    => Syntax.Predicate variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> m (Predicate variable)
simplify predicate = do
    simplified <- simplifyTerm (Syntax.Predicate.unwrapPredicate predicate)
    return $ asPredicate (OrPattern.toPattern simplified)

asPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> Predicate variable
asPredicate Conditional {term, predicate, substitution} =
    let
        andPatt =
            Syntax.Predicate.makeAndPredicate predicate
            $ Syntax.Predicate.wrapPredicate term
    in
        Conditional
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
