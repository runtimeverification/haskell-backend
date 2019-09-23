{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyAndRemoveTopExists
    , simplify
    ) where

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
import Kore.Internal.TermLike
    ( pattern Exists_
    )
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import qualified Kore.Step.Merging.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    , simplifyConditionalTermToOr
    )

simplifyAndRemoveTopExists
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyAndRemoveTopExists patt = do
    simplified <- simplify patt
    return (removeTopExists <$> simplified)
  where
    removeTopExists :: Pattern variable -> Pattern variable
    removeTopExists p@Conditional{ term = Exists_ _ _ quantified } =
        removeTopExists p {term = quantified}
    removeTopExists p = p

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
simplify pattern' = do
    orSimplifiedTerms <- simplifyConditionalTermToOr predicate term
    fmap OrPattern.fromPatterns . Branch.gather $ do
        simplifiedTerm <- Branch.scatter orSimplifiedTerms
        Pattern.mergeWithPredicate predicate simplifiedTerm
  where
    (term, predicate) = Conditional.splitTerm pattern'
