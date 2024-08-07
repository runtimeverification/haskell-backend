{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Booster.Pattern.Existential (matchExistential, instantiateExistentials, instantiateExistentialsMany) where

import Control.Monad (guard, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import Data.Coerce (coerce)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as Set

import Booster.Pattern.Base
import Booster.Pattern.Util

{- | Given a set of @known@ predicates, which must not contains any existential variables,
     attempt to instantiate the existential in the @target@ predicate using the following method:
     * generate a list of candidate substitutions by matching with every known predicate individually
     * collapse all substitutions into one, resolving any conflicts left-to-right, i.e. if a variable
       is bound, it is /not/ updated
-}
instantiateExistentials :: Set Predicate -> Predicate -> (Predicate, Substitution)
instantiateExistentials known target@(Predicate targetTerm) =
    let candidates = map (matchExistential target) (Set.toList known)
        combinedSubst = Map.unions candidates
     in (Predicate $ substituteInTerm combinedSubst targetTerm, combinedSubst)

type Substitution = Map Variable Term

{- | Apply @instantiateExistentials@ to a list of predicates:
     - apply to the head to instantiate existentials and get the substitution
     - apply the substitution to the tail and call recursively
-}
instantiateExistentialsMany :: Set Predicate -> [Predicate] -> [Predicate]
instantiateExistentialsMany known = reverse . go []
  where
    go :: [Predicate] -> [Predicate] -> [Predicate]
    go acc = \case
        [] -> acc
        (p : ps) ->
            let (p', subst) = instantiateExistentials known p
             in go (p' : acc) (map (coerce . substituteInTerm subst . coerce) ps)

{- | Given a @target@ predicate, which may contain existential variables,
  and a @known@ predicate, which must not, attempt to instantiate the first with the second
-}
matchExistential :: Predicate -> Predicate -> Substitution
matchExistential target known =
    flip execState Map.empty . runMaybeT $ matchExistentialImpl target known

matchExistentialImpl :: Predicate -> Predicate -> MaybeT (State Substitution) ()
matchExistentialImpl (Predicate target) (Predicate known) =
    case (target, known) of
        (SymbolApplication symbol1 _ [a, b], SymbolApplication symbol2 _ [c, d]) -> do
            guard (symbol1 == symbol2)
            tryBindExVar a c
            tryBindExVar b d
        _ -> fail "Not a symbol application"
  where
    tryBindExVar :: Term -> Term -> MaybeT (State Substitution) ()
    tryBindExVar variable term = do
        when (isExistentialVariable variable) $ do
            let variableVar = fromJust . retractVariable $ variable
            lift $ modify (Map.insert variableVar term)

isExistentialVariable :: Term -> Bool
isExistentialVariable = \case
    Var v -> isExVar v.variableName
    _ -> False
