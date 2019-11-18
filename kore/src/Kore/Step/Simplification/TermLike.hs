{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import qualified Control.Lens.Combinators as Lens
import Control.Monad
    ( unless
    )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import Data.Maybe
    ( fromMaybe
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import qualified Branch as BranchT
    ( gather
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
    ( mergeAll
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.And as And
    ( simplify
    )
import qualified Kore.Step.Simplification.Application as Application
    ( simplify
    )
import qualified Kore.Step.Simplification.Bottom as Bottom
    ( simplify
    )
import qualified Kore.Step.Simplification.Builtin as Builtin
    ( simplify
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( simplify
    )
import qualified Kore.Step.Simplification.DomainValue as DomainValue
    ( simplify
    )
import qualified Kore.Step.Simplification.Equals as Equals
    ( simplify
    )
import qualified Kore.Step.Simplification.Exists as Exists
    ( simplify
    )
import qualified Kore.Step.Simplification.Floor as Floor
    ( simplify
    )
import qualified Kore.Step.Simplification.Forall as Forall
    ( simplify
    )
import qualified Kore.Step.Simplification.Iff as Iff
    ( simplify
    )
import qualified Kore.Step.Simplification.Implies as Implies
    ( simplify
    )
import qualified Kore.Step.Simplification.In as In
    ( simplify
    )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalBytes as InternalBytes
    ( simplify
    )
import qualified Kore.Step.Simplification.Mu as Mu
    ( simplify
    )
import qualified Kore.Step.Simplification.Next as Next
    ( simplify
    )
import qualified Kore.Step.Simplification.Not as Not
    ( simplify
    )
import qualified Kore.Step.Simplification.Nu as Nu
    ( simplify
    )
import qualified Kore.Step.Simplification.Or as Or
    ( simplify
    )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
    ( simplify
    )
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiableF (Simplified, Unsimplified)
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( freeVariables
    , fromTermLike
    , substitute
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
    ( simplify
    )
import qualified Kore.Step.Simplification.Top as Top
    ( simplify
    )
import qualified Kore.Step.Simplification.Variable as Variable
    ( simplify
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import qualified Kore.Unification.Substitution as Substitution
    ( toMap
    )
import Kore.Unparser
    ( unparse
    , unparseToString
    )
import qualified Kore.Variables.Binding as Binding
import Kore.Variables.Fresh
    ( refreshVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a `TermLike`, returning a 'Pattern'.
-}
simplify
    ::  ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    =>  TermLike variable
    ->  Condition variable
    ->  simplifier (Pattern variable)
simplify patt predicate = do
    orPatt <- simplifyToOr predicate patt
    return (OrPattern.toPattern orPatt)

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    ::  ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    =>  Condition variable
    ->  TermLike variable
    ->  simplifier (OrPattern variable)
simplifyToOr predicate term =
    localSimplifierTermLike (const simplifier)
        . simplifyInternal term
        $ predicate
  where
    simplifier = termLikeSimplifier simplifyToOr

simplifyInternal
    ::  forall variable simplifier
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    =>  TermLike variable
    ->  Condition variable
    ->  simplifier (OrPattern variable)
simplifyInternal term predicate = do
    result <- simplifyIfNeeded term
    unless (OrPattern.isSimplified result)
        (error $ unlines
            (   [ "Not simplified."
                , "result = "
                ]
            ++ map unparseToString (OrPattern.toPatterns result)
            )
        )
    return result
  where
    simplifyIfNeeded :: TermLike variable -> simplifier (OrPattern variable)
    simplifyIfNeeded termLike
      | TermLike.isSimplified termLike
      = case Predicate.makePredicate termLike of
        Left _ -> return . OrPattern.fromTermLike $ termLike
        Right termPredicate ->
            return
            $ OrPattern.fromPattern
            $ Pattern.fromCondition
            $ assertConditionSimplified termLike
            $ Condition.fromPredicate termPredicate
      | otherwise
      = assertTermNotPredicate $ do
        let simplifiableTerm = Simplifiable.fromTermLike term
        simplifyUntilStable simplifiableTerm

    assertConditionSimplified
        :: TermLike variable -> Condition variable -> Condition variable
    assertConditionSimplified originalTerm condition =
        if Condition.isSimplified condition
            then condition
            else (error . unlines)
                [ "Not simplified."
                , "term = "
                , unparseToString originalTerm
                , "condition = "
                , unparseToString condition
                ]
    {-
    tracer termLike = case AxiomIdentifier.matchAxiomIdentifier termLike of
        Nothing -> id
        Just identifier -> Profiler.identifierSimplification identifier
    -- TODO: Move somewhere else.
    -}

    predicateFreeVars =
        FreeVariables.getFreeVariables $ Condition.freeVariables predicate

    simplifyChildren
        :: Traversable t
        => t (Simplifiable variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren = traverse simplifyUntilStable

    applySubstitutionAndResimplifyOr
        :: OrPattern variable
        -> simplifier (OrPattern variable)
    applySubstitutionAndResimplifyOr orPattern = do
        results <- mapM
            applySubstitutionAndResimplifyPattern
            (OrPattern.toPatterns orPattern)
        return (MultiOr.mergeAll results)

    applySubstitutionAndResimplifyPattern
        :: Pattern variable -> simplifier (OrPattern variable)
    applySubstitutionAndResimplifyPattern patt = do
        --traceM ("applySubstitutionAndResimplifyPattern.1 " ++ show (length (show patt)))
        --traceM (unparseToString patt)
        normalized <- normalizeCondition patt
        --traceM ("applySubstitutionAndResimplifyPattern.2 " ++ show (length (show patt)))
        case OrPattern.toPatterns normalized of
            [p] | p == patt -> return (OrPattern.fromPattern patt)
            _ -> do
                --traceM ("applySubstitutionAndResimplifyPattern.3 " ++ show (length (show patt)))
                simplifyInternal (OrPattern.toTermLike normalized) predicate
      where
        normalizeCondition
            ::  Pattern variable ->  simplifier (OrPattern variable)
        normalizeCondition conditional =
            fmap OrPattern.fromPatterns $ BranchT.gather $ do
                let (term', condition') = Pattern.splitTerm conditional
                simplifiedCondition@Conditional{ substitution } <-
                    simplifyCondition condition'
                let substitutedTerm =
                        TermLike.substitute
                            (Substitution.toMap substitution)
                            term'
                return $ Conditional.withCondition
                    substitutedTerm
                    simplifiedCondition

    simplifyUntilStable
        :: Simplifiable variable -> simplifier (OrPattern variable)
    simplifyUntilStable simplifiable = do
        --traceM ("simplifyUntilStable start " ++ show (length (show simplifiable)))
        result <- case Recursive.project simplifiable of
            Simplified result -> do
                --traceM ("simplifyUntilStable result " ++ unlines (unparseToString <$> OrPattern.toPatterns result))
                assertTermNotPredicate $ applySubstitutionAndResimplifyOr result
            Unsimplified unsimplified -> do
                simplifiedOnce <- descendAndSimplify unsimplified
                simplifyUntilStable simplifiedOnce
        --traceM ("simplifyUntilStable end " ++ show (length (show simplifiable)))
        return result

    assertTermNotPredicate getResults = do
        results <- getResults
        let
            -- The term of a result should never be any predicate other than
            -- Top or Bottom.
            hasPredicateTerm Conditional { term = term' }
                | isTop term' || isBottom term' = False
                | otherwise                     = Predicate.isPredicate term'
            unsimplified =
                filter hasPredicateTerm $ OrPattern.toPatterns results
        if null unsimplified
            then return results
            else (error . show . Pretty.vsep)
                [ "Incomplete simplification!"
                , Pretty.indent 2 "input:"
                --, Pretty.indent 4 (unparse termLike)
                , Pretty.indent 2 "unsimplified results:"
                , (Pretty.indent 4 . Pretty.vsep)
                    (unparse <$> unsimplified)
                , "Expected all predicates to be removed from the term."
                ]

    descendAndSimplify
        :: TermLikeF variable (Simplifiable variable)
        -> simplifier (Simplifiable variable)
    descendAndSimplify termLikeF =
        let doNotSimplify = error "Should have already been simplified."
        in case termLikeF of
            -- Unimplemented cases
            ApplyAliasF _ -> doNotSimplify
            -- Do not simplify non-simplifiable patterns.
            EvaluatedF  _ -> doNotSimplify
            EndiannessF _ -> doNotSimplify
            SignednessF _ -> doNotSimplify
            --
            AndF andF -> -- trace ("descendAndSimplify.And " ++ show (length (show termLikeF))) $
                And.simplify =<< simplifyChildren andF
            ApplySymbolF applySymbolF -> --trace ("descendAndSimplify.ApplySymbol " ++ show (length (show termLikeF))) $
                Application.simplify predicate =<< simplifyChildren applySymbolF
            CeilF ceilF -> --trace ("descendAndSimplify.Ceil " ++ show (length (show termLikeF))) $
                Ceil.simplify predicate =<< simplifyChildren ceilF
            EqualsF equalsF -> --trace ("descendAndSimplify.Equals " ++ show (length (show termLikeF))) $
                Equals.simplify =<< simplifyChildren equalsF
            ExistsF exists -> --trace ("descendAndSimplify.Exists " ++ show (length (show termLikeF))) $
                let fresh =
                        Lens.over
                            Binding.existsBinder
                            refreshBinder
                            exists
                in Exists.simplify =<< simplifyChildren fresh
            IffF iffF -> --trace ("descendAndSimplify.Iff " ++ show (length (show termLikeF))) $
                Iff.simplify <$> simplifyChildren iffF
            ImpliesF impliesF -> --trace ("descendAndSimplify.Implies " ++ show (length (show termLikeF))) $
                Implies.simplify <$> simplifyChildren impliesF
            InF inF -> --trace ("descendAndSimplify.In " ++ show (length (show termLikeF))) $
                In.simplify <$> simplifyChildren inF
            NotF notF -> --trace ("descendAndSimplify.Not " ++ show (length (show termLikeF))) $
                Not.simplify <$> simplifyChildren notF
            --
            BottomF bottomF -> --trace ("descendAndSimplify.Bottom " ++ show (length (show termLikeF))) $
                Bottom.simplify <$> simplifyChildren bottomF
            BuiltinF builtinF -> --trace ("descendAndSimplify.Builtin " ++ show (length (show termLikeF))) $
                Builtin.simplify <$> simplifyChildren builtinF
            DomainValueF domainValueF -> --trace ("descendAndSimplify.DomainValue " ++ show (length (show termLikeF))) $
                DomainValue.simplify <$> simplifyChildren domainValueF
            FloorF floorF -> --trace ("descendAndSimplify.Floor " ++ show (length (show termLikeF))) $
                Floor.simplify <$> simplifyChildren floorF
            ForallF forall -> --trace ("descendAndSimplify.Forall " ++ show (length (show termLikeF))) $
                let fresh =
                        Lens.over
                            Binding.forallBinder
                            refreshBinder
                            forall
                in Forall.simplify <$> simplifyChildren fresh
            InhabitantF inhF -> --trace ("descendAndSimplify.Inhabitant " ++ show (length (show termLikeF))) $
                Inhabitant.simplify <$> simplifyChildren inhF
            MuF mu -> --trace ("descendAndSimplify.Mu " ++ show (length (show termLikeF))) $
                let fresh = Lens.over Binding.muBinder refreshBinder mu
                in Mu.simplify <$> simplifyChildren fresh
            NuF nu -> --trace ("descendAndSimplify.Nu " ++ show (length (show termLikeF))) $
                let fresh = Lens.over Binding.nuBinder refreshBinder nu
                in Nu.simplify <$> simplifyChildren fresh
            -- TODO(virgil): Move next up through patterns.
            NextF nextF -> --trace ("descendAndSimplify.Next " ++ show (length (show termLikeF))) $
                Next.simplify <$> simplifyChildren nextF
            OrF orF -> --trace ("descendAndSimplify.Or " ++ show (length (show termLikeF))) $
                Or.simplify <$> simplifyChildren orF
            RewritesF rewritesF -> --trace ("descendAndSimplify.Rewrites " ++ show (length (show termLikeF))) $
                Rewrites.simplify <$> simplifyChildren rewritesF
            TopF topF -> --trace ("descendAndSimplify.Top " ++ show (length (show termLikeF))) $
                Top.simplify <$> simplifyChildren topF
            --
            StringLiteralF stringLiteralF -> --trace ("descendAndSimplify.StringLiteral " ++ show (length (show termLikeF))) $
                return $ StringLiteral.simplify (getConst stringLiteralF)
            InternalBytesF internalBytesF -> --trace ("descendAndSimplify.InternalBytes " ++ show (length (show termLikeF))) $
                return $ InternalBytes.simplify (getConst internalBytesF)
            VariableF variableF -> --trace ("descendAndSimplify.Variable " ++ show (length (show termLikeF))) $
                return $ Variable.simplify (getConst variableF)

    refreshBinder
        :: Binding.Binder (UnifiedVariable variable) (Simplifiable variable)
        -> Binding.Binder (UnifiedVariable variable) (Simplifiable variable)
    refreshBinder binder@Binding.Binder { binderVariable, binderChild }
      | binderVariable `Set.member` predicateFreeVars =
        let existsFreeVars =
                FreeVariables.getFreeVariables
                $ Simplifiable.freeVariables binderChild
            fresh =
                fromMaybe (error "guard above ensures result <> Nothing")
                    $ refreshVariable
                        (predicateFreeVars <> existsFreeVars)
                        binderVariable
            -- TODO(virgil): A variable replacement that does not change the
            -- "simplified" bits may be better.
            freshChild =
                Simplifiable.substitute
                    ( binderVariable
                    , TermLike.mkVar fresh
                    )
                    binderChild
        in Binding.Binder
            { binderVariable = fresh
            , binderChild = freshChild
            }
      | otherwise = binder
