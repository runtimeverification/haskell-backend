{-|
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Procedure
    ( unificationProcedure
    ) where

import           Control.Applicative
                 ( empty )
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Internal.Pattern
                 ( Conditional (..) )
import qualified Kore.Internal.Pattern as Conditional
import           Kore.Internal.Predicate
                 ( Predicate )
import           Kore.Internal.TermLike
import qualified Kore.Logger as Logger
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as BranchT
                 ( scatter )
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMerger )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -- ^left-hand-side of unification
    -> TermLike variable
    -> unifier (Predicate variable)
unificationProcedure substitutionSimplifier simplifier axiomIdToSimplifier p1 p2
  | p1Sort /= p2Sort = do
    Monad.Unify.explainBottom
        "Cannot unify different sorts."
        p1
        p2
    empty
  | otherwise = do
    Monad.Unify.liftSimplifier
        . Logger.withLogScope (Logger.Scope "UnificationProcedure")
        . Logger.logInfo
        . Text.pack
        . show
        $ Pretty.vsep
            [ "Attemptying to unify terms"
            , Pretty.indent 4 $ unparse p1
            , "with"
            , Pretty.indent 4 $ unparse p2
            ]
    tools <- Monad.Unify.liftSimplifier Simplifier.askMetadataTools
    let
        getUnifiedTerm =
            termUnification
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                p1
                p2
    pat@Conditional { term } <- getUnifiedTerm
    if Conditional.isBottom pat
        then empty
        else Monad.Unify.liftBranchedSimplifier $ do
            orCeil <-
                Monad.Trans.lift $ Ceil.makeEvaluateTerm
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    term
            orResult <-
                OrPattern.mergeWithPredicateAssumesEvaluated
                    (createPredicatesAndSubstitutionsMerger
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                    )
                    (Conditional.withoutTerm pat)
                    orCeil
            BranchT.scatter (MultiOr.extractPatterns orResult)
  where
      p1Sort = termLikeSort p1
      p2Sort = termLikeSort p2
