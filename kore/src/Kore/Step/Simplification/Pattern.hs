{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    , simplify
    ) where

import Branch
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
    ( topTODO
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import Kore.Internal.TermLike
    ( pattern Exists_
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    , simplifyCondition
    , simplifyConditionalTermToOr
    )

{-| Simplifies the pattern without a side-condition (i.e. it's top)
and removes the exists quantifiers at the top.
-}
simplifyTopConfiguration
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyTopConfiguration patt = do
    simplified <- simplify Condition.topTODO patt
    return (removeTopExists <$> simplified)
  where
    removeTopExists :: Pattern variable -> Pattern variable
    removeTopExists p@Conditional{ term = Exists_ _ _ quantified } =
        removeTopExists p {term = quantified}
    removeTopExists p = p

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    :: SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
simplify sideCondition pattern' = do
    orSimplifiedTerms <- simplifyConditionalTermToOr predicate term
    fmap OrPattern.fromPatterns . Branch.gather $ do
        simplifiedTerm <- Branch.scatter orSimplifiedTerms
        simplifyCondition sideCondition
            (Conditional.andCondition simplifiedTerm predicate)
  where
    (term, predicate) = Conditional.splitTerm pattern'
