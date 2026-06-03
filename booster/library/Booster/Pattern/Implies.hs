{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Booster.Pattern.Implies (runImplies) where

import Control.Monad (unless)
import Control.Monad.Extra (void)
import Control.Monad.Trans.Except (runExcept)
import Data.Coerce (coerce)
import Data.Data (Proxy)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text (Text, pack)
import Data.Text qualified as Text
import Network.JSONRPC (ErrorObj)

import Booster.Definition.Base (KoreDefinition)
import Booster.LLVM qualified
import Booster.Log (getPrettyModifiers)
import Booster.Log qualified
import Booster.Pattern.ApplyEquations qualified as ApplyEquations
import Booster.Pattern.Base (Pattern (..), Predicate (..))
import Booster.Pattern.Bool (pattern TrueBool)
import Booster.Pattern.Match (FailReason (..), MatchResult (..), MatchType (Implies), matchTerms)
import Booster.Pattern.Pretty (FromModifiersT, ModifiersRep (..), pretty')
import Booster.Pattern.Substitution (asEquations)
import Booster.Pattern.Util (freeVariables, sortOfPattern)
import Booster.Prettyprinter (renderDefault)
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.Json (addHeader, prettyPattern)
import Booster.Syntax.Json.Externalise (
    externaliseExistTerm,
    externaliseSort,
    externaliseSubstitution,
 )
import Booster.Syntax.Json.Internalise (
    PatternOrTopOrBottom (..),
    internalisePatternOrTopOrBottom,
    logPatternError,
    patternErrorToRpcError,
    pattern CheckSubsorts,
    pattern DisallowAlias,
 )
import Booster.Syntax.ParsedKore.Internalise (extractExistentials)
import Booster.Util (constructorName)

import Kore.JsonRpc.Error qualified as RpcError
import Kore.JsonRpc.Types qualified as RpcTypes
import Kore.Syntax.Json.Types qualified as Kore.Syntax

runImplies ::
    Booster.Log.LoggerMIO m =>
    KoreDefinition ->
    Maybe Booster.LLVM.API ->
    Maybe SMT.SMTOptions ->
    Kore.Syntax.KoreJson ->
    Kore.Syntax.KoreJson ->
    m (Either ErrorObj (RpcTypes.API 'RpcTypes.Res))
runImplies def mLlvmLibrary mSMTOptions antecedent consequent =
    getPrettyModifiers >>= \case
        ModifiersRep (_ :: FromModifiersT mods => Proxy mods) -> Booster.Log.withContext Booster.Log.CtxImplies $ do
            solver <- maybe (SMT.noSolver) (SMT.initSolver def) mSMTOptions
            -- internalise given constrained term
            let internalised korePat' =
                    let (korePat, existentials) = extractExistentials korePat'
                     in runExcept $
                            internalisePatternOrTopOrBottom DisallowAlias CheckSubsorts Nothing def existentials korePat

                checkImplies patL unsupportedL existsL patR unsupportedR existsR = do
                    let substitutionL = patL.substitution
                        substitutionR = patR.substitution
                        freeVarsL =
                            ( freeVariables patL.term
                                <> (Set.unions $ Set.map (freeVariables . coerce) patL.constraints)
                                <> (Set.fromList $ Map.keys substitutionL)
                            )
                                Set.\\ Set.fromList existsL
                        freeVarsR =
                            ( freeVariables patR.term
                                <> (Set.unions $ Set.map (freeVariables . coerce) patR.constraints)
                                <> (Set.fromList $ Map.keys substitutionR)
                            )
                                Set.\\ Set.fromList existsR
                        freeVarsRminusL = freeVarsR Set.\\ freeVarsL
                    if
                        | not $ null freeVarsRminusL ->
                            pure . Left . RpcError.backendError . RpcError.ImplicationCheckError $
                                RpcError.ErrorWithContext "The RHS must not have free variables not present in the LHS" $
                                    map (pack . renderDefault . pretty' @mods) $
                                        Set.toList freeVarsRminusL
                        | not (null unsupportedL) || not (null unsupportedR) -> do
                            Booster.Log.logMessage
                                ("aborting due to unsupported predicate parts" :: Text)
                            unless (null unsupportedL) $
                                Booster.Log.withContext Booster.Log.CtxDetail $
                                    Booster.Log.logMessage
                                        (Text.unwords $ map prettyPattern unsupportedL)
                            unless (null unsupportedR) $
                                Booster.Log.withContext Booster.Log.CtxDetail $
                                    Booster.Log.logMessage
                                        (Text.unwords $ map prettyPattern unsupportedR)
                            pure . Left . RpcError.backendError . RpcError.ImplicationCheckError $
                                RpcError.ErrorWithContext "Could not internalise part of the configuration" $
                                    map (pack . show) $
                                        unsupportedL <> unsupportedR
                        | otherwise -> do
                            SMT.isSat solver (Set.toList patL.constraints) patL.substitution >>= \case
                                SMT.IsUnsat ->
                                    let sort = externaliseSort $ sortOfPattern patL
                                     in implies' (Kore.Syntax.KJBottom sort) sort antecedent.term consequent.term mempty
                                _ -> checkImpliesMatchTerms existsL patL existsR patR

                checkImpliesMatchTerms existsL patL existsR patR =
                    case matchTerms Booster.Pattern.Match.Implies def patR.term patL.term of
                        MatchFailed (SubsortingError sortError) ->
                            pure . Left . RpcError.backendError . RpcError.ImplicationCheckError . RpcError.ErrorOnly . pack $
                                show sortError
                        MatchFailed{} ->
                            doesNotImply
                                (sortOfPattern patL)
                                (externaliseExistTerm existsL patL.term)
                                (externaliseExistTerm existsR patR.term)
                        MatchIndeterminate _partialSubst _remainder ->
                            ApplyEquations.evaluatePatternWithCeils def mLlvmLibrary solver mempty patL >>= \case
                                (Right simplifedSubstPatL, _) ->
                                    if patL == simplifedSubstPatL
                                        then
                                            doesNotImply
                                                (sortOfPattern patL)
                                                (externaliseExistTerm existsL patL.term)
                                                (externaliseExistTerm existsR patR.term)
                                        else checkImpliesMatchTerms existsL simplifedSubstPatL existsR patR
                                (Left err, _) ->
                                    pure . Left . RpcError.backendError $ RpcError.Aborted (Text.pack . constructorName $ err)
                        MatchSuccess subst -> do
                            let sort = sortOfPattern patL
                                lhs = externaliseExistTerm existsL patL.term
                                rhs = externaliseExistTerm existsR patR.term
                                antecedentPreds =
                                    patL.constraints <> Set.fromList (asEquations patL.substitution)
                                filteredConsequentPreds =
                                    (patR.constraints <> Set.fromList (asEquations patR.substitution))
                                        `Set.difference` antecedentPreds
                            if null filteredConsequentPreds
                                then implies sort lhs rhs subst
                                else do
                                    -- Discharge the leftover consequent obligations under
                                    -- the antecedent. Two stages:
                                    --   1. Simplify each obligation with the antecedent in
                                    --      'knownPredicates' so function-symbol unfolds
                                    --      (e.g. '#rangeAddress') and boolean structure
                                    --      collapse can fire.
                                    --   2. SMT-close any non-'TrueBool' residue against
                                    --      'antecedentPreds' / 'patL.substitution' — the
                                    --      same pattern the rewrite path uses to discharge
                                    --      rule requires-clauses
                                    --      ('Booster.Pattern.Rewrite.checkRequires').
                                    simplified <-
                                        mapM
                                            ( fmap fst
                                                . ApplyEquations.simplifyConstraint
                                                    def
                                                    mLlvmLibrary
                                                    solver
                                                    mempty
                                                    antecedentPreds
                                            )
                                            (Set.toList filteredConsequentPreds)
                                    let impliesResult = implies sort lhs rhs subst
                                        unsure = doesNotImplyIndeterminate sort lhs rhs
                                        disjoint = doesNotImply sort lhs rhs
                                    case sequence simplified of
                                        Left _ ->
                                            -- Equation engine error: route to Unsure
                                            -- rather than the old hard 'Aborted', so the
                                            -- client can escalate via kore fallback.
                                            unsure
                                        Right reduced
                                            | all (== Predicate TrueBool) reduced ->
                                                impliesResult
                                            | otherwise -> do
                                                let residue =
                                                        Set.fromList $
                                                            filter (/= Predicate TrueBool) reduced
                                                SMT.checkPredicates
                                                    solver
                                                    antecedentPreds
                                                    patL.substitution
                                                    residue
                                                    >>= \case
                                                        SMT.IsValid -> impliesResult
                                                        SMT.IsInvalid -> disjoint
                                                        -- Vacuous antecedent: any consequent
                                                        -- is implied.
                                                        SMT.IsUnknown SMT.InconsistentGroundTruth ->
                                                            impliesResult
                                                        SMT.IsUnknown _ -> unsure

            case (internalised antecedent.term, internalised consequent.term) of
                (Left patternError, _) -> do
                    void $ Booster.Log.withContext Booster.Log.CtxInternalise $ logPatternError patternError
                    pure $
                        Left $
                            RpcError.backendError $
                                RpcError.CouldNotVerifyPattern
                                    [ patternErrorToRpcError patternError
                                    ]
                (_, Left patternError) -> do
                    void $ Booster.Log.withContext Booster.Log.CtxInternalise $ logPatternError patternError
                    pure $
                        Left $
                            RpcError.backendError $
                                RpcError.CouldNotVerifyPattern
                                    [ patternErrorToRpcError patternError
                                    ]
                (Right (IsBottom sort), Right _) ->
                    implies' (Kore.Syntax.KJBottom sort) sort antecedent.term consequent.term mempty
                (Right IsTop{}, _) ->
                    pure . Left . RpcError.backendError . RpcError.ImplicationCheckError . RpcError.ErrorOnly $
                        "The check implication step expects the antecedent term to be function-like."
                ( Right (IsPattern (existsL, patL, unsupportedL))
                    , Right (IsPattern (existsR, patR, unsupportedR))
                    ) ->
                        checkImplies patL unsupportedL existsL patR unsupportedR existsR
                (Right IsPattern{}, Right (IsTop sort)) ->
                    implies' (Kore.Syntax.KJTop sort) sort antecedent.term consequent.term mempty
                (Right IsPattern{}, Right (IsBottom sort)) ->
                    doesNotImply'
                        sort
                        ( Just $
                            RpcTypes.Condition
                                { predicate = addHeader $ Kore.Syntax.KJBottom sort
                                , substitution = addHeader $ Kore.Syntax.KJTop sort
                                }
                        )
                        antecedent.term
                        consequent.term
  where
    -- Single construction point for every implies / does-not-imply result.
    -- The call sites differ only in 'valid', 'condition', and 'indeterminate';
    -- centralising the record keeps a future field addition a one-line change.
    mkResult s l r valid condition indeterminate =
        pure . Right . RpcTypes.Implies $
            RpcTypes.ImpliesResult
                { implication = addHeader $ Kore.Syntax.KJImplies s l r
                , valid
                , condition
                , logs = Nothing
                , indeterminate
                }

    doesNotImply' s condition l r = mkResult s l r False condition Nothing

    doesNotImply s' = let s = externaliseSort s' in doesNotImply' s Nothing

    -- Variant of 'doesNotImply' that flags the result as indeterminate.
    -- Use at non-decisive 'valid = False' outcomes — the 'MatchIndeterminate'
    -- retry-ladder no-progress fall-through and the 'MatchSuccess'
    -- SMT-discharge 'IsUnknown _' branch — so a recover-mode client
    -- escalates to kore rather than trusting @valid: false@.
    doesNotImplyIndeterminate s' l r =
        let s = externaliseSort s' in mkResult s l r False Nothing (Just True)

    implies' predicate s l r subst =
        mkResult s l r True (Just condition) Nothing
      where
        condition =
            RpcTypes.Condition
                { predicate = addHeader predicate
                , substitution =
                    addHeader
                        $ ( \case
                                [] -> Kore.Syntax.KJTop s
                                [x] -> x
                                xs -> Kore.Syntax.KJAnd s xs
                          )
                            . map (uncurry $ externaliseSubstitution s)
                            . Map.toList
                        $ subst
                }
    implies s' = let s = externaliseSort s' in implies' (Kore.Syntax.KJTop s) s
