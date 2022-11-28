{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Unify (
    module Kore.Pattern.Unify,
) where

import Control.Monad
import Control.Monad.Extra (whenJust)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Either.Extra
import Data.Foldable (toList)
import Data.List.NonEmpty as NE (NonEmpty ((:|)), singleton)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set

import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Pattern.Util (freeVariables, isConstructorSymbol, sortOfTerm, substituteInTerm)

-- | Result of a unification (a substitution or an indication of what went wrong)
data UnificationResult
    = -- | equal structure (constructors) after substitution (substitution goes both ways)
      UnificationSuccess Substitution
    | -- | different constructors or domain values, or sort mismatch
      UnificationFailed FailReason
    | -- | (other) cases that are unresolved (offending case in head position).
      UnificationRemainder (NonEmpty (Term, Term))
    | InternalError String
    deriving stock (Eq, Show)

-- | Additional information to explain why a unification has failed
data FailReason
    = -- | (Domain) values differ
      DifferentValues Term Term
    | -- | Symbols differ
      DifferentSymbols Term Term
    | -- | Variable would refer to itself. FIXME should not happen at
      -- all. Need to rename rule variables to avoid it.
      VariableRecursion Variable Term
    | -- | Variable reassigned
      VariableConflict Variable Term Term
    deriving stock (Eq, Show)

type Substitution = Map Variable Term

{- | Attempts to find a simple unifying substitution for the given
   terms. Only constructor symbols are considered (no functions).

   The returned substitution is oriented towards 'term1', i.e.,
   prefers to replace its variables if given a choice.
-}
unifyTerms :: KoreDefinition -> Term -> Term -> UnificationResult
unifyTerms KoreDefinition{sorts} term1 term2 =
    let runUnification :: UnificationState -> UnificationResult
        runUnification =
            fromEither
                . runExcept
                . fmap (UnificationSuccess . uSubstitution)
                . execStateT unification
        freeVars1 = freeVariables term1
        freeVars2 = freeVariables term2
        sharedVars = freeVars1 `Set.intersection` freeVars2
     in if not $ Set.null sharedVars
            then UnificationRemainder $ NE.singleton (term1, term2)
            else
                runUnification
                    State
                        { uSubstitution = Map.empty
                        , uTargetVars = freeVars1
                        , uQueue = Seq.singleton (term1, term2)
                        , uSubsorts = Map.map snd sorts
                        }

data UnificationState = State
    { uSubstitution :: Substitution
    , uTargetVars :: Set Variable
    , uQueue :: Seq (Term, Term) -- work queue (breadth-first term traversal)
    , uSubsorts :: SortTable
    }

type SortTable = Map SortName (Set SortName)

unification :: StateT UnificationState (Except UnificationResult) ()
unification = do
    queue <- gets uQueue
    case queue of
        Empty -> pure () -- done
        (term1, term2) :<| rest -> do
            modify $ \s -> s{uQueue = rest}
            unify1 term1 term2
            unification

unify1 ::
    Term ->
    Term ->
    StateT UnificationState (Except UnificationResult) ()
-- two domain values: have to fully agree
unify1
    d1@(DomainValue s1 t1)
    d2@(DomainValue s2 t2) =
        do
            unless (t1 == t2) $
                failWith (DifferentValues d1 d2)
            unless (s1 == s2) $ -- sorts must be exactly the same for DVs
                returnAsRemainder d1 d2

-- two symbol applications: fail if names differ, recurse
unify1
    t1@(SymbolApplication symbol1 args1)
    t2@(SymbolApplication symbol2 args2) =
        do
            subsorts <- gets uSubsorts
            -- argument sorts have been checked upon internalisation
            unless (sortsAgree subsorts symbol1.resultSort symbol2.resultSort) $
                returnAsRemainder t1 t2
            -- If we have functions, pass - only constructors are matched.
            unless (isConstructorSymbol symbol1 && isConstructorSymbol symbol2) $
                returnAsRemainder t1 t2
            -- constructors must be the same
            unless (symbol1.name == symbol2.name) $
                failWith (DifferentSymbols t1 t2)
            unless (length args1 == length args2) $
                lift $
                    throwE $
                        InternalError $
                            "Argument counts differ for same constructor" <> show (t1, t2)
            zipWithM_ enqueueProblem args1 args2

-- and-term in pattern: must unify with both arguments
unify1
    (AndTerm t1a t1b)
    term2 =
        do
            enqueueProblem t1a term2
            enqueueProblem t1b term2
-- and-term in subject: must unify with both arguments
unify1
    term1
    (AndTerm t2a t2b) =
        do
            enqueueProblem term1 t2a
            enqueueProblem term1 t2b

-- twice the exact same variable: verify sorts are equal
unify1
    (Var var1@(Variable varSort1 varName1))
    (Var var2@(Variable varSort2 varName2))
        -- same variable: forbidden!
        | var1 == var2 =
            lift $ throwE $ InternalError $ "Shared variable: " <> show var1
        | varName1 == varName2 && varSort1 /= varSort2 =
            -- sorts differ, names equal: error!
            failWith $ VariableConflict var1 (Var var1) (Var var2)
-- term1 variable (target): introduce a new binding
unify1
    (Var var@Variable{variableSort})
    term2 =
        do
            subsorts <- gets uSubsorts
            let termSort = sortOfTerm term2
            unless (sortsAgree subsorts variableSort termSort) $
                returnAsRemainder (Var var) term2
            bindVariable var term2

-- term2 variable (not target), term1 not a variable: swap arguments (won't recurse)
unify1
    term1
    v@Var{} =
        unify1 v term1
-- Remaining other cases: mix of DomainValue and SymbolApplication (either side)
-- The remaining unification problems are returned
unify1
    t1@SymbolApplication{}
    t2@DomainValue{} =
        returnAsRemainder t1 t2
unify1
    t1@DomainValue{}
    t2@SymbolApplication{} =
        returnAsRemainder t1 t2

failWith :: FailReason -> StateT s (Except UnificationResult) ()
failWith = lift . throwE . UnificationFailed

enqueueProblem :: Monad m => Term -> Term -> StateT UnificationState m ()
enqueueProblem term1 term2 =
    modify $ \s@State{uQueue} -> s{uQueue = uQueue :|> (term1, term2)}

{- | Binds a variable to a term to add to the resulting unifier.

 We apply the accumulated substitution whenever a new variable
 binding to a term is added. This avoids repeated traversals while
 guarding against substitution loops.
-}
bindVariable :: Variable -> Term -> StateT UnificationState (Except UnificationResult) ()
bindVariable var term = do
    State{uSubstitution = currentSubst, uTargetVars = targets} <- get
    case term of
        -- Check if term is a variable, prefer target variables. Should
        -- not happen given how we call it in the code above.
        Var var2
            | var2 `Set.member` targets
                && not (var `Set.member` targets) ->
                bindVariable var2 (Var var)
        -- regular case
        _other -> do
            let mbOldTerm = Map.lookup var currentSubst
            whenJust mbOldTerm $ \oldTerm ->
                -- TODO the term in the binding could be _equivalent_
                -- (not necessarily syntactically equal) to term'
                failWith $ VariableConflict var oldTerm term
            let -- apply existing substitutions to term
                term' = substituteInTerm currentSubst term
            when (var `Set.member` freeVariables term') $
                failWith (VariableRecursion var term)
            let -- substitute in existing substitution terms
                currentSubst' = Map.map (substituteInTerm $ Map.singleton var term') currentSubst
            let newSubst = Map.insert var term' currentSubst'
            modify $ \s -> s{uSubstitution = newSubst}

returnAsRemainder :: Term -> Term -> StateT UnificationState (Except UnificationResult) ()
returnAsRemainder t1 t2 = do
    remainder <- gets uQueue
    lift $ throwE $ UnificationRemainder $ (t1, t2) :| toList remainder

{- | Checks that 's2' can be used for 's1', i.e., is a subsort.

 Current implementation only checks sort equality, and does not
 handle sort variables. Result 'False' must mean _indeterminate
 unification_, not failing unification!
-}
sortsAgree :: SortTable -> Sort -> Sort -> Bool
-- do not consider variables (we would need to carry a sort
-- variable substitution in the state to check consistency)
sortsAgree _ SortVar{} _ = False
sortsAgree _ _ SortVar{} = False
-- only accept syntactically equal sorts
sortsAgree st (SortApp sort1 args1) (SortApp sort2 args2) =
    sort1 == sort2
        && length args1 == length args2
        && and (zipWith (sortsAgree st) args1 args2)
