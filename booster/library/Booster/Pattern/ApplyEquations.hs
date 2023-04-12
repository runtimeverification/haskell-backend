{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.ApplyEquations (
    module Booster.Pattern.ApplyEquations,
) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Data.Functor.Foldable
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.Base
import Booster.Pattern.Index
import Booster.Pattern.Match
import Booster.Pattern.Simplify
import Booster.Pattern.Util

newtype EquationM rule err a = EquationM (StateT (EquationState rule) (Except err) a)
    deriving newtype (Functor, Applicative, Monad)

throw :: err -> EquationM tag err a
throw = EquationM . lift . throwE

data EquationFailure a
    = IndexIsNone Term
    | InconsistentFunctionRules [a]
    | IndeterminateMatch a a
    | IndeterminateCondition Predicate
    | TooManyIterations Int a a
    | InternalError Text
    deriving stock (Eq, Show)

data EquationState rule = EquationState
    { definition :: KoreDefinition
    , theory :: Theory rule
    , llvmApi :: Maybe LLVM.API
    , hasChanged :: Bool
    , counter :: Int
    }

startState :: KoreDefinition -> Theory rule -> Maybe LLVM.API -> EquationState rule
startState definition theory llvmApi =
    EquationState{definition, theory, llvmApi, hasChanged = False, counter = 0}

increment, markChanged, clearChanged :: EquationM rule err ()
increment = EquationM . modify $ \s -> s{counter = 1 + s.counter}
markChanged = EquationM . modify $ \s -> s{hasChanged = True}
clearChanged = EquationM . modify $ \s -> s{hasChanged = False}

getState :: EquationM rule err (EquationState rule)
getState = EquationM get

getCounter :: EquationM rule err Int
getCounter = (.counter) <$> getState

getChanged :: EquationM rule err Bool
getChanged = (.hasChanged) <$> getState

data Direction = TopDown | BottomUp
    deriving stock (Eq, Show)

runEquationM ::
    KoreDefinition ->
    Maybe LLVM.API ->
    Theory rule ->
    EquationM rule err a ->
    Either err a
runEquationM definition llvmApi theory (EquationM m) =
    runExcept $ evalStateT m $ startState definition theory llvmApi

iterateWithEquations ::
    forall tag.
    ApplyEquationOps tag =>
    Int ->
    Direction ->
    KoreDefinition ->
    Maybe LLVM.API ->
    (KoreDefinition -> Theory (RewriteRule tag)) ->
    Term ->
    Either (EquationFailure Term) Term
iterateWithEquations maxIterations direction def llvmApi getEquations startTerm =
    runEquationM def llvmApi (getEquations def) (go startTerm)
  where
    go :: Term -> EquationM (RewriteRule tag) (EquationFailure Term) Term
    go currentTerm =
        do
            currentCount <- getCounter
            when (currentCount > maxIterations) $
                throw $
                    TooManyIterations currentCount startTerm currentTerm
            newTerm <- applyTerm direction currentTerm
            changeFlag <- getChanged
            if changeFlag
                then increment >> clearChanged >> go newTerm
                else pure currentTerm

----------------------------------------
-- Interface functions
simplify
    , evaluateFunctions ::
        Direction ->
        KoreDefinition ->
        Maybe LLVM.API ->
        Term ->
        Either (EquationFailure Term) Term
simplify direction definition llvmApi =
    iterateWithEquations 20 direction definition llvmApi (.simplifications)
evaluateFunctions direction definition llvmApi =
    iterateWithEquations 100 direction definition llvmApi (.functionEquations)

----------------------------------------

{- | Apply the set of equations in the equation state at all levels of a
   term AST, in the given direction (bottom-up or top-down).

  No iteration happens at the same AST level inside these traversals,
  one equation will be applied per level (if any).
-}
applyTerm ::
    forall tag.
    ApplyEquationOps tag =>
    Direction ->
    Term ->
    EquationM (RewriteRule tag) (EquationFailure Term) Term
applyTerm BottomUp =
    cataA $ \case
        DomainValueF s val ->
            pure $ DomainValue s val
        VarF var ->
            pure $ Var var
        InjectionF src trg t ->
            Injection src trg <$> t -- no injection simplification
        AndTermF arg1 arg2 ->
            AndTerm <$> arg1 <*> arg2 -- no \and simplification
        SymbolApplicationF sym sorts args -> do
            t <- SymbolApplication sym sorts <$> sequence args
            applyAtTop t
applyTerm TopDown = \case
    dv@DomainValue{} ->
        pure dv
    v@Var{} ->
        pure v
    Injection src trg t ->
        Injection src trg <$> applyTerm TopDown t -- no injection simplification
    AndTerm arg1 arg2 ->
        AndTerm <$> applyTerm TopDown arg1 <*> applyTerm TopDown arg2 -- no \and simplification
    app@(SymbolApplication sym sorts args) -> do
        -- try to apply equations
        t <- applyAtTop app
        if (getAttributes t).hash /= (getAttributes app).hash
            then do
                case t of
                    SymbolApplication sym' sorts' args' ->
                        SymbolApplication sym' sorts' <$> mapM (applyTerm TopDown) args'
                    _otherwise ->
                        applyTerm TopDown t -- won't loop
            else SymbolApplication sym sorts <$> mapM (applyTerm TopDown) args

{- | Try to apply all equations from the state to the given term, in
   priority order and per group.
-}
applyAtTop ::
    forall tag.
    ApplyEquationOps tag =>
    Term ->
    EquationM (RewriteRule tag) (EquationFailure Term) Term
applyAtTop term = do
    EquationState{theory} <- getState
    let index = termTopIndex term
    when (index == None) $
        throw (IndexIsNone term)
    let idxEquations, anyEquations :: Map Priority [RewriteRule tag]
        idxEquations = fromMaybe Map.empty $ Map.lookup index theory
        anyEquations = fromMaybe Map.empty $ Map.lookup Anything theory
        equationGroups :: [[RewriteRule tag]]
        equationGroups =
            map snd . Map.toAscList $
                if index == Anything
                    then idxEquations
                    else Map.unionWith (<>) idxEquations anyEquations

    -- no need for an error when (null equationGroups), it will just stop.
    processGroups equationGroups
  where
    -- process one group of equations at a time, until something has happened
    processGroups ::
        [[RewriteRule tag]] ->
        EquationM (RewriteRule tag) (EquationFailure Term) Term
    processGroups [] =
        pure term -- nothing to do, term stays the same
    processGroups (eqs : rest) = do
        -- try all equations in this group, and inspect the results
        results <- catMaybes <$> mapM (applyEquation term) eqs
        case results of
            [] ->
                processGroups rest -- no success at all in this group
            [newTerm] -> do
                markChanged
                pure newTerm -- single result
            (first : second : more) -> do
                markChanged
                onMultipleResults (Proxy @tag) first (second :| more)

applyEquation ::
    forall tag.
    ApplyEquationOps tag =>
    Term ->
    RewriteRule tag ->
    EquationM (RewriteRule tag) (EquationFailure Term) (Maybe Term)
applyEquation term rule = runMaybeT $ do
    -- ensured by internalisation: no existentials in equations
    unless (null rule.existentials) $
        lift . throw . InternalError $
            "Equation with existentials: " <> Text.pack (show rule)
    -- immediately cancel if not preserving definedness
    guard rule.computedAttributes.preservesDefinedness
    -- match lhs
    koreDef <- (.definition) <$> lift getState
    case matchTerm koreDef rule.lhs.term term of
        MatchFailed _failReason -> do
            -- some logging, then
            fail "match failed"
        MatchIndeterminate pat subj -> do
            -- some logging, then
            onIndeterminateMatch (Proxy @tag) pat subj
        MatchError msg ->
            lift . throw . InternalError $ "Match error: " <> msg
        MatchSuccess subst -> do
            -- check conditions, using substitution (will call back
            -- into the simplifier! -> import loop)
            let newConstraints =
                    concatMap (splitBoolPredicates . substituteInPredicate subst) $
                        rule.lhs.constraints <> rule.rhs.constraints
            unclearConditions <- catMaybes <$> mapM checkConstraint newConstraints

            unless (null unclearConditions) $
                onIndeterminateCondition (Proxy @tag) (head unclearConditions)
            let rewritten =
                    substituteInTerm subst rule.rhs.term
            -- NB no new constraints, as they have been checked to be `Top`
            -- FIXME what about symbolic constraints here?
            return rewritten
  where
    -- evaluate/simplify a predicate, cut the operation short when it
    -- is Bottom.
    checkConstraint ::
        Predicate ->
        MaybeT (EquationM (RewriteRule tag) (EquationFailure Term)) (Maybe Predicate)
    checkConstraint p = do
        mApi <- (.llvmApi) <$> lift getState
        case simplifyPredicate mApi p of
            Bottom -> fail "side condition was false"
            Top -> pure Nothing
            _other -> pure $ Just p

--------------------------------------------------------------------

{- | Type class to encapsulate the differences between applying
   simplifications and applying function rules.
-}
class ApplyEquationOps (tag :: k) where
    -- | Behaviour when several equations in a priority group match:
    --
    -- * for '"Simplification"' equations, choose the first matching
    --   equation
    -- * for '"Function"' equations, having several equations at the
    --   same priority match is an error, and equations are reported.
    onMultipleResults ::
        Proxy tag ->
        Term ->
        NonEmpty Term ->
        EquationM (RewriteRule tag) (EquationFailure Term) Term

    -- | Behaviour when a match cannot be determined
    --
    -- * for '"Simplification"' equations, discard and proceed
    -- * for '"Function"' equations, abort evaluation (equations at
    --   lower priority should not be tried)
    onIndeterminateMatch ::
        Proxy tag ->
        Term ->
        Term ->
        MaybeT (EquationM (RewriteRule tag) (EquationFailure Term)) Term

    -- | Behaviour when side conditions cannot be determined
    --
    -- * for '"Simplification"' equations, discard and proceed
    -- * for '"Function"' equations, abort evaluation (equations at
    --   lower priority should not be tried)
    onIndeterminateCondition ::
        Proxy tag ->
        Predicate ->
        MaybeT (EquationM (RewriteRule tag) (EquationFailure Term)) ()

instance ApplyEquationOps "Simplification" where
    -- choose first result if more than one
    onMultipleResults _ one _ = pure one

    -- continue with more equations if application indeterminate
    onIndeterminateMatch _ _ _ = fail "indeterminate match"
    onIndeterminateCondition _ _ = fail "indeterminate condition"

instance ApplyEquationOps "Function" where
    -- report that equations are non-deterministic
    onMultipleResults _ one (another :| more) =
        -- FIXME should contain the equations not the terms
        throw $ InconsistentFunctionRules (one : another : more)

    -- throw error (abort evaluation) when indeterminate match
    -- (subsequent equations at lower priority cannot be used)
    onIndeterminateMatch _ pat subj =
        lift $ throw $ IndeterminateMatch pat subj

    -- abort further evaluation when a side condition is indeterminate
    -- (subsequent equations at lower priority cannot be used)
    onIndeterminateCondition _ p =
        lift $ throw $ IndeterminateCondition p
