{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    , simplify
    ) where

import Prelude.Kore

import Branch
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    , topTODO
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
    simplified <- simplify SideCondition.topTODO patt
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
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
simplify sideCondition pattern' = do
    -- TODO(virgil): simplify the predicate first.
    orSimplifiedTerms <- simplifyConditionalTermToOr termSideCondition term
    fmap OrPattern.fromPatterns . Branch.gather $ do
        simplifiedTerm <- Branch.scatter orSimplifiedTerms
        simplifyCondition sideCondition
            (Conditional.andCondition simplifiedTerm condition)
  where
    (term, condition) = Conditional.splitTerm pattern'
    termSideCondition = sideCondition `SideCondition.andCondition` condition
