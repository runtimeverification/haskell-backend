{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.SMT.Interface (
    SMTContext, -- re-export
    SMTOptions (..),
    defaultSMTOptions,
    initSolver,
    closeSolver,
    getModelFor,
    checkPredicates,
) where

import Control.Monad
import Control.Monad.Logger qualified as Log
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.ByteString.Char8 qualified as BS
import Data.Coerce
import Data.Either (isLeft)
import Data.Either.Extra (fromLeft', fromRight')
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text as Text (Text, pack, unpack, unwords)

import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Util (sortOfTerm)
import Booster.SMT.Base as SMT
import Booster.SMT.Runner as SMT
import Booster.SMT.Translate as SMT

newtype SMTOptions = SMTOptions
    { transcript :: Maybe FilePath
    }
    deriving (Eq, Show)

defaultSMTOptions :: SMTOptions
defaultSMTOptions = SMTOptions{transcript = Nothing}

initSolver :: Log.MonadLoggerIO io => KoreDefinition -> SMTOptions -> io SMT.SMTContext
initSolver def smtOptions = do
    ctxt <- mkContext smtOptions.transcript
    logSMT "Checking definition prelude"
    let prelude = smtDeclarations def
    case prelude of
        Left err -> do
            logSMT $ "Error translating definition to SMT: " <> err
            error $ "Unable to translate elements of the definition to SMT: " <> Text.unpack err
        Right{} -> pure ()
    check <-
        runSMT ctxt $
            mapM_ runCmd (fromRight' prelude) >> runCmd CheckSat
    case check of
        Sat -> pure ctxt
        other -> do
            logSMT $ "Initial SMT definition check returned " <> pack (show other)
            error "Refusing to work with a potentially inconsistent SMT setup"

closeSolver :: Log.MonadLoggerIO io => SMT.SMTContext -> io ()
closeSolver ctxt = do
    logSMT "Closing SMT solver"
    closeContext ctxt

{- |
Implementation of get-model request

Queries an SMT solver (given by SMTContext but assumed uninitialised,
passing the definition) for whether the given predicates and
the supplied substitution are satisfiable together.

Returns a satisfying substitution of free variables
in the predicates if so.

Returns either 'Unsat' or 'Unknown' otherwise, depending on whether
the solver could determine 'Unsat'.
-}
getModelFor ::
    Log.MonadLoggerIO io =>
    SMT.SMTContext ->
    [Predicate] ->
    Map Variable Term -> -- supplied substitution
    io (Either SMT.Response (Map Variable Term))
getModelFor ctxt ps subst
    | null ps && Map.null subst = do
        logSMT "No constraints or substitutions to check, returning Sat"
        pure $ Right Map.empty
    | otherwise = runSMT ctxt $ do
        logSMT $ "Checking, constraint count " <> pack (show $ Map.size subst + length ps)
        let translated =
                SMT.runTranslator $ do
                    let mkSMTEquation v t =
                            SMT.eq <$> SMT.translateTerm (Var v) <*> SMT.translateTerm t
                    smtSubst <-
                        mapM (fmap Assert . uncurry mkSMTEquation) $ Map.assocs subst
                    smtPs <-
                        mapM (fmap Assert . SMT.translateTerm . coerce) ps
                    pure $ smtSubst <> smtPs
            freeVars =
                Set.unions $
                    Map.keysSet subst : map ((.variables) . getAttributes . coerce) ps
        when (isLeft translated) $
            error . Text.unpack $
                fromLeft' translated
        let (smtAsserts, transState) = fromRight' translated
            freeVarsMap =
                Map.filterWithKey
                    (const . (`Set.member` Set.map Var freeVars))
                    transState.mappings
            freeVarsToSExprs = Map.mapKeys getVar $ Map.map Atom freeVarsMap

        runCmd_ SMT.Push -- assuming the prelude has been run already,

        -- declare-const all introduced variables (free in predicates
        -- as well as abstraction variables) before sending assertions
        mapM_
            runCmd
            [ DeclareConst smtId (SMT.smtSort $ sortOfTerm trm)
            | (trm, smtId) <- Map.assocs transState.mappings
            ]

        -- assert the given predicates
        mapM_ runCmd smtAsserts

        satResponse <- runCmd CheckSat

        case satResponse of
            Error msg -> do
                runCmd_ SMT.Pop
                error $ "SMT Error: " <> BS.unpack msg
            Unsat -> do
                runCmd_ SMT.Pop
                pure $ Left Unsat
            Unknown -> do
                runCmd_ SMT.Pop
                pure $ Left Unknown
            Values{} -> do
                runCmd_ SMT.Pop
                error $ "Unexpected SMT response " <> show satResponse
            Success -> do
                runCmd_ SMT.Pop
                error $ "Unexpected SMT response " <> show satResponse
            Sat -> do
                response <-
                    if Map.null freeVarsToSExprs
                        then pure $ Values []
                        else runCmd $ GetValue (Map.elems freeVarsToSExprs)
                runCmd_ SMT.Pop
                case response of
                    Error msg ->
                        error $ "SMT Error: " <> BS.unpack msg
                    Values pairs ->
                        let (errors, values) =
                                Map.partition isLeft
                                    . Map.map (valueToTerm transState)
                                    $ Map.compose (Map.fromList pairs) freeVarsToSExprs
                         in if null errors
                                then pure $ Right $ Map.map fromRight' values
                                else
                                    error . unlines $
                                        ( "SMT errors while converting results: "
                                            : map (Text.unpack . fromLeft') (Map.elems errors)
                                        )
                    other ->
                        error $ "Unexpected SMT response to GetValue: " <> show other
  where
    getVar (Var v) = v
    getVar _ = error "not a var"

{- | Check a predicates, given a set of predicates as known truth.

Simplest version:

Given K as known truth and predicates P to check, check whether K => P
or K => !P, or neither of those implications holds. The check is done
by asking the solver to find a counter-example:

- If K ∧ !P yields Unsat then K => P (P is true given K)
- If K ∧ P yields Unsat then K => !P (P is false given K)

For both cases, the respective other result should be Sat, not
Unknown, but we can _assume_ that by excluded middle (P ∨ !P).

- If both K ∧ !P and K ∧ P yield Unsat then K is already Unsat (i.e.,
  false) by itself and we should not conclude anything.
- All other cases imply that we cannot conclude any impliciation,
  neither P nor !P follows from K.

In the initial version we make no attempt to determine _which_ of the
predicates in P contributes to the respective false result. Neither do
we check whether the predicates in P are satisfiable at all by
themselves (together, without constraints in K).
-}
checkPredicates ::
    forall io.
    Log.MonadLoggerIO io =>
    SMT.SMTContext ->
    Set Predicate ->
    Map Variable Term ->
    Set Predicate ->
    io (Maybe Bool)
checkPredicates ctxt givenPs givenSubst psToCheck
    | null psToCheck = pure $ Just True -- or Nothing?
    | Left errMsg <- translated = do
        Log.logErrorNS "booster" $ "SMT translation error: " <> errMsg
        pure Nothing
    | Right ((smtGiven, sexprsToCheck), transState) <- translated = runSMT ctxt . runMaybeT $ do
        logSMT $
            Text.unwords
                [ "Checking"
                , pack (show $ length psToCheck)
                , "predicates, given"
                , pack (show $ length givenPs)
                , "assertions and a substitution of size"
                , pack (show $ Map.size givenSubst)
                ]

        smtRun_ Push

        -- declare-const all introduced variables (free in predicates
        -- as well as abstraction variables) before sending assertions
        mapM_
            smtRun
            [ DeclareConst smtId (SMT.smtSort $ sortOfTerm trm)
            | (trm, smtId) <- Map.assocs transState.mappings
            ]

        -- assert ground truth
        mapM_ smtRun smtGiven

        consistent <- smtRun CheckSat
        when (consistent /= Sat) $ do
            void $ smtRun Pop
            logSMT "Inconsistent ground truth, check returns Nothing"
            fail "returns nothing"

        -- save ground truth for 2nd check
        smtRun_ Push

        -- run check for K ∧ P and then for K ∧ !P
        let allToCheck = SMT.List (Atom "and" : sexprsToCheck)

        smtRun_ $ Assert allToCheck
        positive <- smtRun CheckSat
        smtRun_ Pop
        smtRun_ $ Assert (SMT.smtnot allToCheck)
        negative <- smtRun CheckSat
        void $ smtRun Pop

        logSMT $
            "Check of Given ∧ P and Given ∧ !P produced "
                <> pack (show (positive, negative))

        case (positive, negative) of
            (Unsat, Unsat) -> fail "should have been caught above"
            (_, Unsat) -> pure True
            (Unsat, _) -> pure False
            _anythingElse_ -> fail "Both Sat, Unknown results, or error"
  where
    smtRun_ :: SMTEncode c => c -> MaybeT (SMT io) ()
    smtRun_ = lift . SMT.runCmd_
    smtRun :: SMTEncode c => c -> MaybeT (SMT io) Response
    smtRun = lift . SMT.runCmd

    translated = SMT.runTranslator $ do
        let mkSMTEquation v t =
                SMT.eq <$> SMT.translateTerm (Var v) <*> SMT.translateTerm t
        smtSubst <-
            mapM (fmap Assert . uncurry mkSMTEquation) $ Map.assocs givenSubst
        smtPs <-
            mapM (fmap Assert . SMT.translateTerm . coerce) $ Set.toList givenPs
        toCheck <-
            mapM (SMT.translateTerm . coerce) $ Set.toList psToCheck
        pure (smtSubst <> smtPs, toCheck)

logSMT :: Log.MonadLoggerIO io => Text -> io ()
logSMT = Log.logOtherNS "booster" (Log.LevelOther "SMT")
