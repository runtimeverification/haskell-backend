{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Match (
    MatchResult (..),
    MatchFailReason (..),
    PredicatesDoNotMatch (..),
    matchTerm,
    matchPredicate,
) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Bifunctor (second)
import Data.Either.Extra
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Sequence (Seq (..), (><))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set

import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Unify (FailReason (..), SortError, checkSubsort)
import Booster.Pattern.Util (
    checkSymbolIsAc,
    freeVariables,
    modifyVariablesInP,
    sortOfTerm,
    substituteInTerm,
 )

-- | Result of matching a pattern to a subject (unification, failure, or indeterminate)
data MatchResult
    = -- | found a matching substitution
      MatchSuccess (Map Variable Term)
    | -- | pattern and subject have differences (using same failure type as unification)
      MatchFailed MatchFailReason
    | -- | match cannot be determined
      MatchIndeterminate Term Term
    deriving stock (Eq, Show)

data MatchFailReason
    = -- | shared with unification
      General FailReason
    | -- | Shared variables between matching terms
      SharedVariables (Set Variable)
    | -- | Subsorting related errors
      SubsortingError SortError
    | -- | The two terms have differing argument lengths
      ArgLengthsDiffer Term Term
    deriving stock (Eq, Show)

{- | Attempts to find a matching substitution for the given
   term1 to term2.

  Symbols (functions and constructors) are matched syntactically,
  i.e., when present in the pattern (term1) they also need to be
  present in the subject (term2).
-}
matchTerm :: KoreDefinition -> Term -> Term -> MatchResult
matchTerm KoreDefinition{sorts} term1 term2 =
    let runMatching :: MatchState -> MatchResult
        runMatching =
            fromEither
                . runExcept
                . fmap (MatchSuccess . mSubstitution)
                . execStateT matching
        freeVars1 = freeVariables term1
        freeVars2 = freeVariables term2
        sharedVars = freeVars1 `Set.intersection` freeVars2
     in if not $ Set.null sharedVars
            then MatchFailed $ SharedVariables sharedVars
            else
                runMatching
                    State
                        { mSubstitution = Map.empty
                        , mQueue = Seq.singleton (term1, term2)
                        , mSubsorts = Map.map snd sorts
                        }

data MatchState = State
    { mSubstitution :: Map Variable Term
    , mQueue :: Seq (Term, Term) -- work queue
    , mSubsorts :: Map SortName (Set SortName)
    }

matching :: StateT MatchState (Except MatchResult) ()
matching = do
    queue <- gets mQueue
    case queue of
        Empty -> pure () -- done
        (term1, term2) :<| rest -> do
            modify $ \s -> s{mQueue = rest}
            match1 term1 term2
            matching

match1 ::
    Term ->
    Term ->
    StateT MatchState (Except MatchResult) ()
----- Variables
-- pattern term is a (target) variable: check sorts, introduce a new binding
match1
    term1@(Var var@Variable{variableSort})
    term2 =
        do
            let termSort = sortOfTerm term2
            subsorts <- gets mSubsorts
            isSubsort <-
                lift . withExcept (MatchFailed . SubsortingError) $
                    checkSubsort subsorts termSort variableSort
            unless isSubsort $
                failWith $
                    DifferentSorts term1 term2
            -- TODO are subsorts allowed?
            bindVariable
                var
                ( if termSort == variableSort
                    then term2
                    else Injection termSort variableSort term2
                )
----- Domain values
-- two domain values: have to fully agree
match1
    d1@(DomainValue s1 t1)
    d2@(DomainValue s2 t2) =
        do
            unless (t1 == t2) $
                failWith (DifferentValues d1 d2)
            unless (s1 == s2) $ -- sorts must be exactly the same for DVs
                failWith (DifferentSorts d1 d2)
-- subject not a domain value
match1
    d1@DomainValue{}
    term2 =
        failWith $ DifferentValues d1 term2
----- And Terms
-- and-term in pattern: must unify with both arguments (typically used
-- to bind variables while also matching)
match1
    (AndTerm t1a t1b)
    term2 =
        do
            enqueueProblem t1a term2
            enqueueProblem t1b term2
----- Injections
-- two injections. Try to unify the contained terms if the sorts
-- agree. Target sorts must be the same, source sorts may differ if
-- the contained pattern term is just a variable, otherwise they need
-- to be identical.
match1
    pat@(Injection source1 target1 trm1)
    subj@(Injection source2 target2 trm2)
        | target1 /= target2 = do
            failWith (DifferentSorts pat subj)
        | source1 == source2 = do
            enqueueProblem trm1 trm2
        | Var v <- trm1 = do
            -- variable in pattern, check source sorts and bind
            subsorts <- gets mSubsorts
            isSubsort <-
                lift . withExcept (MatchFailed . SubsortingError) $
                    checkSubsort subsorts source2 source1
            if isSubsort
                then bindVariable v (Injection source2 source1 trm2)
                else failWith (DifferentSorts trm1 trm2)
        | otherwise =
            failWith (DifferentSorts pat subj)
-- injection in pattern, no injection in subject: fail
match1
    inj@Injection{}
    trm =
        failWith $ DifferentSymbols inj trm
----- Symbol Applications
-- two symbol applications: fail if names differ, recurse
match1
    t1@(SymbolApplication symbol1 sorts1 args1)
    t2@(SymbolApplication symbol2 sorts2 args2)
        | symbol1.name /= symbol2.name = failWith (DifferentSymbols t1 t2)
        | length args1 /= length args2 =
            lift $ throwE $ MatchFailed $ ArgLengthsDiffer t1 t2
        | sorts1 /= sorts2 = failWith (DifferentSorts t1 t2)
        | checkSymbolIsAc symbol1 =
            -- If the symbol is non-free (AC symbol), return indeterminate
            lift $ throwE $ MatchIndeterminate t1 t2
        | otherwise =
            enqueueProblems $ Seq.fromList $ zip args1 args2
-- subject not a symbol application: fail
match1
    t1@SymbolApplication{}
    t2 =
        failWith $ DifferentSymbols t1 t2
-- matching on maps unsupported
match1
    t1@KMap{}
    t2 =
        lift $ throwE $ MatchIndeterminate t1 t2

failWith :: FailReason -> StateT s (Except MatchResult) ()
failWith = lift . throwE . MatchFailed . General

enqueueProblem :: Monad m => Term -> Term -> StateT MatchState m ()
enqueueProblem term1 term2 =
    modify $ \s@State{mQueue} -> s{mQueue = mQueue :|> (term1, term2)}

enqueueProblems :: Monad m => Seq (Term, Term) -> StateT MatchState m ()
enqueueProblems ts =
    modify $ \s@State{mQueue} -> s{mQueue = mQueue >< ts}

{- | Binds a variable to a term to add to the resulting unifier.

 We apply the accumulated substitution whenever a new variable
 binding to a term is added. This avoids repeated traversals while
 guarding against substitution loops.
-}
bindVariable :: Variable -> Term -> StateT MatchState (Except MatchResult) ()
bindVariable var term = do
    currentSubst <- gets mSubstitution
    case Map.lookup var currentSubst of
        Just oldTerm
            | oldTerm == term -> pure () -- already bound
            | otherwise ->
                -- only consider full syntactic match, not equivalence
                failWith $ VariableConflict var oldTerm term
        Nothing -> do
            let
                -- apply existing substitutions to term
                term' = substituteInTerm currentSubst term
            when (var `Set.member` freeVariables term') $
                failWith (VariableRecursion var term)
            let
                -- substitute in existing substitution terms
                currentSubst' =
                    Map.map (substituteInTerm $ Map.singleton var term') currentSubst
                newSubst = Map.insert var term' currentSubst'
            modify $ \s -> s{mSubstitution = newSubst}

----------------------------------------

{- | Match a predicate pattern (containing terms) to a predicate
   subject.

  Since the result is a variable substitution and variables are terms,
  this will ultimately fall back to matching terms. The predicate is
  traversed, collecting a queue of term matching problems to run once
  the predicate shapes are matched completely.

  An additional error type is added for the case where the predicate
  pattern does not match the subject syntactically.

  This is kept simple because we don't expect to use is much; only
  few simplifications on ML constructs are allowed and used.
-}
matchPredicate ::
    KoreDefinition ->
    Predicate ->
    Predicate ->
    Either PredicatesDoNotMatch MatchResult
matchPredicate def pat subj =
    second runTermMatching $ matchPredicates (pat, subj)
  where
    runTermMatching :: Seq (Term, Term) -> MatchResult
    runTermMatching =
        fromEither
            . runExcept
            . fmap (MatchSuccess . mSubstitution)
            . execStateT matching
            . mkMatchState

    -- produce initial state with given work queue
    mkMatchState mQueue =
        State{mSubstitution = Map.empty, mQueue, mSubsorts = Map.map snd def.sorts}

    matchPredicates :: (Predicate, Predicate) -> Either PredicatesDoNotMatch (Seq (Term, Term))
    matchPredicates = runExcept . execWriterT . collect

    collect :: (Predicate, Predicate) -> WriterT (Seq (Term, Term)) (Except PredicatesDoNotMatch) ()
    collect (pPattern, pSubject) = case (pPattern, pSubject) of
        (AndPredicate p1 p2, AndPredicate s1 s2) ->
            collect (p1, s1) >> collect (p2, s2)
        (Bottom, Bottom) ->
            pure ()
        (Ceil p, Ceil s) ->
            enqueue (p, s)
        (EqualsTerm p1 p2, EqualsTerm s1 s2) ->
            enqueue (p1, s1) >> enqueue (p2, s2)
        (EqualsPredicate p1 p2, EqualsPredicate s1 s2) ->
            collect (p1, s1) >> collect (p2, s2)
        (Exists pv p, Exists sv s) -> do
            -- forbid pv in the resulting substitution by injecting it here
            enqueue (Var pv, Var sv)
            let renamedS = modifyVariablesInP (renameVariable sv pv) s
            collect (p, renamedS)
        (Forall pv p, Forall sv s) -> do
            -- forbid pv in the resulting substitution by injecting it here
            enqueue (Var pv, Var sv)
            let renamedS = modifyVariablesInP (renameVariable sv pv) s
            collect (p, renamedS)
        (Iff p1 p2, Iff s1 s2) ->
            collect (p1, s1) >> collect (p2, s2)
        (Implies p1 p2, Implies s1 s2) ->
            collect (p1, s1) >> collect (p2, s2)
        (In p1 p2, In s1 s2) ->
            enqueue (p1, s1) >> enqueue (p2, s2)
        (Not p, Not s) ->
            collect (p, s)
        (Or p1 p2, Or s1 s2) ->
            collect (p1, s1) >> collect (p2, s2)
        (Top, Top) ->
            pure ()
        _other -> noMatch
      where
        enqueue = tell . Seq.singleton
        noMatch = lift $ throwE PredicatesDoNotMatch{pPattern, pSubject}

        renameVariable :: Variable -> Variable -> Variable -> Variable
        renameVariable before after target
            | target == before = after
            | target == after = error "variable name capture"
            -- should never happen, equation variables will all be renamed
            | otherwise = target

data PredicatesDoNotMatch = PredicatesDoNotMatch
    { pPattern :: Predicate
    , pSubject :: Predicate
    }
    deriving (Eq, Show)
