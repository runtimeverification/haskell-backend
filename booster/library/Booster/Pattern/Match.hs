{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Match (
    MatchResult (..),
    MatchFailReason (..),
    matchTerm,
    matchPredicate,
) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Bifunctor (first)
import Data.Either.Extra
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), (><))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Prettyprinter

import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Unify (FailReason (..), SortError, checkSubsort)
import Booster.Pattern.Util (
    checkSymbolIsAc,
    freeVariables,
    isConcrete,
    isConstructorSymbol,
    isFunctionSymbol,
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

instance Pretty MatchFailReason where
    pretty = \case
        General reason -> pretty reason
        SharedVariables vs -> "Shared variables:" <+> hsep (map pretty $ Set.toList vs)
        SubsortingError err -> pretty $ show err
        ArgLengthsDiffer t1 t2 -> vsep ["Argument length differ", pretty t1, pretty t2]

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
                        , mMapQueue = mempty
                        , mSubsorts = Map.map snd sorts
                        }

data MatchState = State
    { mSubstitution :: Map Variable Term
    , mQueue :: Seq (Term, Term) -- work queue
    , mMapQueue :: Seq (Term, Term) -- work queue for Map/Set matching (2nd priority)
    , mSubsorts :: Map SortName (Set SortName)
    }

matching :: StateT MatchState (Except MatchResult) ()
matching = do
    st <- get
    case st.mQueue of
        (term1, term2) :<| rest -> do
            modify $ \s -> s{mQueue = rest}
            match1 term1 term2
            matching
        Empty ->
            case st.mMapQueue of
                (term1, term2) :<| rest -> do
                    modify $ \s -> s{mMapQueue = rest}
                    match1 term1 term2
                    matching
                Empty -> pure () -- done

match1 ::
    Term ->
    Term ->
    StateT MatchState (Except MatchResult) ()
----- Variables
-- pattern term is a (target) variable: check sorts, introduce a new binding

-- Matching term2 with term1, when term2 is a variable is safe here,
-- because functional equations are ordered.
-- Consider a function f:
--
--   rule f(foo(A)) => baz() [priority(40)]
--   rule f(A) => A
-- where foo() is a constructor and A is a variable.
--
-- We can safely match f(foo(X)) and rewrite to baz(), because there
-- are no preceding equations involving the constructor foo.
--
-- If instead there was a higher-priority rule
--
--   rule f(foo(bar())) => flob() [priority(30)]
--
-- the preceding match would be indeterminate and the function
-- application would be aborted before reaching the
--   f(foo(A)) => baz()
-- case.
--
-- Finally, if the rules had the opposite priorities
--
--   rule f(foo(A)) => baz()      [priority(30)]
--   rule f(foo(bar())) => flob() [priority(40)]
--   rule f(A) => A
--
-- Since function equations are ordered, the pattern
--    f(foo(bar())) => flob()
-- would be unreachable anyway, hence
--   f(foo(A)) => baz()
-- must always apply to f(foo(X))
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
-- subject term is a variable but pattern term is not: indeterminate
match1
    pat
    var@Var{} =
        indeterminate pat var
-- and-terms in subject term are considered indeterminate
-- (what would they mean?)
match1
    pat
    andTerm@AndTerm{} =
        indeterminate pat andTerm
----- Domain values
match1
    d1@(DomainValue s1 t1)
    subj =
        case subj of
            -- two domain values: have to fully agree
            DomainValue s2 t2 -> do
                unless (t1 == t2) $
                    failWith (DifferentValues d1 subj)
                unless (s1 == s2) $ -- sorts must be exactly the same for DVs
                    failWith (DifferentSorts d1 subj)
            SymbolApplication sym _ _
                -- subject is function application (unevaluated): indeterminate
                | isFunctionSymbol sym -> indeterminate d1 subj
                -- subject is constructor: fail
                | otherwise -> failWith $ DifferentValues d1 subj
            -- Var{} case caught above
            -- injections, and-terms, maps: fail
            _other ->
                failWith $ DifferentValues d1 subj
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
match1
    inj@(Injection source1 target1 trm1)
    subj =
        case subj of
            -- matching two injections:
            -- Try to unify the contained terms if the sorts
            -- agree. Target sorts must be the same, source sorts may
            -- differ if the contained pattern term is just a
            -- variable, otherwise they need to be identical.
            Injection source2 target2 trm2
                | target1 /= target2 -> do
                    failWith (DifferentSorts inj subj)
                | source1 == source2 -> do
                    enqueueProblem trm1 trm2
                | Var v <- trm1 -> do
                    -- variable in pattern, check source sorts and bind
                    subsorts <- gets mSubsorts
                    isSubsort <-
                        lift . withExcept (MatchFailed . SubsortingError) $
                            checkSubsort subsorts source2 source1
                    if isSubsort
                        then bindVariable v (Injection source2 source1 trm2)
                        else failWith (DifferentSorts trm1 trm2)
                | otherwise ->
                    failWith (DifferentSorts inj subj)
            -- injection in pattern, unevaluated function call in
            -- subject: indeterminate
            SymbolApplication sym _ _
                | isFunctionSymbol sym -> indeterminate inj subj
                | otherwise -> failWith $ DifferentSymbols inj subj
            -- injection in pattern, no injection in subject: fail
            -- Var{} case caught above
            -- and, domain values, maps: fail
            _other ->
                failWith $ DifferentSymbols inj subj
----- Symbol Applications
match1
    app@(SymbolApplication symbol1 sorts1 args1)
    subj =
        case subj of
            -- two symbol applications: fail if names differ, match
            -- argument count and sorts, recurse
            SymbolApplication symbol2 sorts2 args2
                | symbol1.name /= symbol2.name ->
                    if isConstructorSymbol symbol1 && isConstructorSymbol symbol2
                        then failWith (DifferentSymbols app subj)
                        else indeterminate app subj
                | length args1 /= length args2 ->
                    lift $ throwE $ MatchFailed $ ArgLengthsDiffer app subj
                | sorts1 /= sorts2 ->
                    failWith (DifferentSorts app subj)
                -- If the symbol is non-free (AC symbol), return indeterminate
                | checkSymbolIsAc symbol1 ->
                    indeterminate app subj
                | otherwise ->
                    enqueueProblems $ Seq.fromList $ zip args1 args2
            -- subject not a symbol application: fail
            -- Var{} case caught above
            -- and, domain values, injections, maps: fail
            _other ->
                failWith $ DifferentSymbols app subj
----- KMap
match1
    t1@(KMap patDef patKeyVals patRest)
    t2@(KMap subjDef subjKeyVals subjRest) = do
        -- different map sorts do not match
        unless (patDef == subjDef) $
            failWith (DifferentSorts t1 t2)
        st <- get
        if not (Seq.null st.mQueue)
            then -- delay matching 'KMap's until there are no regular
            -- problems left, to obtain a maximal prior substitution
            -- before matching map keys.
                enqueueMapProblem t1 t2
            else do
                -- first apply current substitution to pattern key-value pairs
                let patternKeyVals = map (first (substituteInTerm st.mSubstitution)) patKeyVals

                -- check for duplicate keys
                checkDuplicateKeys (KMap patDef patternKeyVals patRest)
                checkDuplicateKeys t2

                let patMap = Map.fromList patternKeyVals
                    subjMap = Map.fromList subjKeyVals
                    -- handles syntactically identical keys in pattern and subject
                    commonMap = Map.intersectionWith (,) patMap subjMap
                    patExtra = patMap `Map.withoutKeys` Map.keysSet commonMap
                    subjExtra = subjMap `Map.withoutKeys` Map.keysSet commonMap

                -- Before enqueueing the common elements for matching,
                -- check whether we can abort early
                case (Map.null patExtra, Map.null subjExtra) of
                    (True, True) ->
                        -- all keys are common, handle opaque rest (if any)
                        case patRest of
                            Nothing ->
                                maybe (pure ()) (enqueueProblem emptyMap) subjRest
                            Just pRest ->
                                enqueueProblem pRest $ fromMaybe emptyMap subjRest
                    (True, False) ->
                        -- subject has extra assocs to match with pattern rest
                        let subj' = KMap subjDef (Map.assocs subjExtra) subjRest
                         in case patRest of
                                Nothing ->
                                    failWith $ DifferentValues emptyMap subj'
                                Just pRest -> do
                                    enqueueProblem pRest subj'
                    (False, True) ->
                        -- pattern has extra assocs
                        let pat' = KMap patDef (Map.assocs patExtra) patRest
                         in case subjRest of
                                Nothing ->
                                    -- no opaque rest, match is definitely failing
                                    failWith $ DifferentValues pat' emptyMap
                                Just sRest ->
                                    -- indeterminate matching with an opaque rest
                                    indeterminate pat' sRest
                    (False, False)
                        -- Special case: definitely fail if all (extra) pattern keys are concrete
                        -- and there is no opaque subject rest
                        | Nothing <- subjRest
                        , all isConcrete (Map.keys patExtra) ->
                            let pat' = KMap patDef (Map.assocs patExtra) patRest
                                subj' = KMap subjDef (Map.assocs subjExtra) subjRest
                             in failWith $ DifferentValues pat' subj'
                        -- Special case: attempt a match if pattern and subject assocs
                        -- are singleton and there is no opaque subject rest
                        | Nothing <- subjRest
                        , [(pKey, pVal)] <- Map.assocs patExtra
                        , [(sKey, sVal)] <- Map.assocs subjExtra -> do
                            let opaque = case patRest of
                                    Nothing -> []
                                    Just rest -> [(rest, emptyMap)]
                            enqueueProblems . Seq.fromList $ (pKey, sKey) : (pVal, sVal) : opaque
                        | otherwise ->
                            indeterminate t1 t2

                -- enqueue common elements for matching unless already failed
                enqueueProblems $ Seq.fromList $ Map.elems commonMap
      where
        emptyMap = KMap patDef [] Nothing

        checkDuplicateKeys m@(KMap _ assocs _) =
            let duplicates =
                    Map.filter (> (1 :: Int)) $ foldr (flip (Map.insertWith (+)) 1 . fst) mempty assocs
             in case Map.assocs duplicates of
                    [] -> pure ()
                    (k, _) : _ -> failWith $ DuplicateKeys k m
        checkDuplicateKeys _ = pure ()

--- not matching map patterns with anything else
match1
    t1@KMap{}
    t2 = indeterminate t1 t2
-- no matching for lists, return indeterminate for now
match1
    t1@KList{}
    t2 = indeterminate t1 t2
-- no matching for sets, return indeterminate for now
match1
    t1@KSet{}
    t2 = indeterminate t1 t2

failWith :: FailReason -> StateT s (Except MatchResult) ()
failWith = lift . throwE . MatchFailed . General

indeterminate :: Term -> Term -> StateT s (Except MatchResult) ()
indeterminate t1 t2 = lift . throwE $ MatchIndeterminate t1 t2

enqueueProblem :: Monad m => Term -> Term -> StateT MatchState m ()
enqueueProblem term1 term2 =
    modify $ \s@State{mQueue} -> s{mQueue = mQueue :|> (term1, term2)}

enqueueMapProblem :: Monad m => Term -> Term -> StateT MatchState m ()
enqueueMapProblem term1 term2 =
    modify $ \s@State{mMapQueue} -> s{mMapQueue = mMapQueue :|> (term1, term2)}

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

{- | Match a predicate pattern (containing boolean terms) to a predicate
   subject, by matching the contained terms.

  This will probably not be used in the booster, as we only accept
  predicates which are boolean terms compared to true or false.
-}
matchPredicate ::
    KoreDefinition ->
    Predicate ->
    Predicate ->
    MatchResult
matchPredicate def (Predicate pat) (Predicate subj) =
    matchTerm def pat subj
