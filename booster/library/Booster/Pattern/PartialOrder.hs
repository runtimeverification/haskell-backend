{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Booster.Pattern.PartialOrder (transitiveClosure) where

import Control.Monad (guard)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Booster.Pattern.Base

{- | Given a set of predicates @ps@, construct a syntactic transitive closure of relative to the symbol @sym@.

     This function only returns new predicates (if any).

     If the @ps@ contains application of symbols other than @sym@, they are ignored.
-}
transitiveClosure :: Symbol -> Set Predicate -> Set Predicate
transitiveClosure sym ps =
    let attempts = map (\target -> Attempt target (Set.toList (Set.delete target ps))) . Set.toList $ ps
     in (Set.fromList . concatMap (makeTransitiveStep sym) $ attempts)

-- | An @Attempt@ is a target clause and a list of assumption clauses
data Attempt = Attempt
    { target :: !Predicate
    -- ^ target predicate to eliminate, contains an existential variable
    , assumptions :: ![Predicate]
    -- ^ predicates that are assume "known", must contain the same existential that the target
    }

{- | Validate a predicate clause. Checks:
     * the clause is a symbol application of @sym@
     * the variables have distinct names, i.e. @sym@ is irreflexive
-}
validateClause :: Symbol -> Predicate -> Bool
validateClause sym (Predicate p) = case p of
    (SymbolApplication clauseSym _ [(Var Variable{variableName = a}), (Var Variable{variableName = b})]) -> clauseSym == sym && a /= b
    _ -> False

-- | Try solving, return an instantiated target if successful
makeTransitiveStep :: Symbol -> Attempt -> [Predicate]
makeTransitiveStep sym Attempt{target, assumptions} = do
    guard (all (validateClause sym) (target : assumptions))
    mapMaybe (matchAndTransit sym target) assumptions

{- | Try to make strengthen the @left@ predicate using the @right@ predicate,
  assuming both are the same *transitive* symbol
-}
matchAndTransit :: Symbol -> Predicate -> Predicate -> Maybe Predicate
matchAndTransit sym (Predicate current) (Predicate next) =
    case (current, next) of
        (SymbolApplication symbol1 sorts [a, b], SymbolApplication symbol2 _ [c, d]) -> do
            guard (symbol1 == symbol2 && b == c)
            let newClause = Predicate $ SymbolApplication symbol1 sorts [a, d]
            guard (validateClause sym newClause)
            pure newClause
        _ -> Nothing
