{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import           Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import qualified Kore.Step.Simplification.And as And
                 ( simplify )
import qualified Kore.Step.Simplification.Application as Application
                 ( simplify )
import qualified Kore.Step.Simplification.Bottom as Bottom
                 ( simplify )
import qualified Kore.Step.Simplification.Builtin as Builtin
                 ( simplify )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( simplify )
import qualified Kore.Step.Simplification.CharLiteral as CharLiteral
                 ( simplify )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.DomainValue as DomainValue
                 ( simplify )
import qualified Kore.Step.Simplification.Equals as Equals
                 ( simplify )
import qualified Kore.Step.Simplification.Exists as Exists
                 ( simplify )
import qualified Kore.Step.Simplification.Floor as Floor
                 ( simplify )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( simplify )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( simplify )
import qualified Kore.Step.Simplification.Implies as Implies
                 ( simplify )
import qualified Kore.Step.Simplification.In as In
                 ( simplify )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant
                 ( simplify )
import qualified Kore.Step.Simplification.Mu as Mu
                 ( simplify )
import qualified Kore.Step.Simplification.Next as Next
                 ( simplify )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplify )
import qualified Kore.Step.Simplification.Nu as Nu
                 ( simplify )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplify )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
                 ( simplify )
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
                 ( simplify )
import qualified Kore.Step.Simplification.Top as Top
                 ( simplify )
import qualified Kore.Step.Simplification.Variable as Variable
                 ( simplify )

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a `TermLike`, returning a 'Pattern'.
-}
simplify
    :: SimplifierVariable variable
    => TermLike variable
    -> Predicate variable
    -> Simplifier (Pattern variable)
simplify patt predicate = do
    orPatt <- simplifyToOr predicate patt
    return (OrPattern.toPattern orPatt)

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Predicate variable
    -> TermLike variable
    -> simplifier (OrPattern variable)
simplifyToOr term predicate =
    localSimplifierTermLike (const simplifier)
        . simplifyInternal predicate
        $ term
  where
    simplifier = termLikeSimplifier simplifyToOr

simplifyInternal
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> Predicate variable
    -> simplifier (OrPattern variable)
simplifyInternal term predicate = simplifyInternalWorker term
  where
    simplifyChildren
        :: Traversable t
        => t (TermLike variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren = traverse simplifyInternalWorker

    simplifyInternalWorker termLike =
        let doNotSimplify = return (OrPattern.fromTermLike termLike)
            (_ :< termLikeF) = Recursive.project termLike
        in case termLikeF of
            -- Unimplemented cases
            ApplyAliasF _ -> doNotSimplify
            -- Do not simplify evaluated patterns.
            EvaluatedF  _ -> doNotSimplify
            --
            AndF andF ->
                And.simplify =<< simplifyChildren andF
            ApplySymbolF applySymbolF ->
                Application.simplify predicate
                    =<< simplifyChildren applySymbolF
            CeilF ceilF ->
                Ceil.simplify predicate =<< simplifyChildren ceilF
            EqualsF equalsF ->
                Equals.simplify predicate =<< simplifyChildren equalsF
            ExistsF existsF ->
                Exists.simplify =<< simplifyChildren existsF
            IffF iffF ->
                Iff.simplify =<< simplifyChildren iffF
            ImpliesF impliesF ->
                Implies.simplify =<< simplifyChildren impliesF
            InF inF ->
                In.simplify predicate =<< simplifyChildren inF
            NotF notF ->
                Not.simplify =<< simplifyChildren notF
            --
            BottomF bottomF -> Bottom.simplify <$> simplifyChildren bottomF
            BuiltinF builtinF -> Builtin.simplify <$> simplifyChildren builtinF
            DomainValueF domainValueF ->
                DomainValue.simplify <$> simplifyChildren domainValueF
            FloorF floorF -> Floor.simplify <$> simplifyChildren floorF
            ForallF forallF -> Forall.simplify <$> simplifyChildren forallF
            InhabitantF inhF -> Inhabitant.simplify <$> simplifyChildren inhF
            MuF muF -> Mu.simplify <$> simplifyChildren muF
            NuF nuF -> Nu.simplify <$> simplifyChildren nuF
            -- TODO(virgil): Move next up through patterns.
            NextF nextF -> Next.simplify <$> simplifyChildren nextF
            OrF orF -> Or.simplify <$> simplifyChildren orF
            RewritesF rewritesF ->
                Rewrites.simplify <$> simplifyChildren rewritesF
            TopF topF -> Top.simplify <$> simplifyChildren topF
            --
            StringLiteralF stringLiteralF ->
                return $ StringLiteral.simplify (getConst stringLiteralF)
            CharLiteralF charLiteralF ->
                return $ CharLiteral.simplify (getConst charLiteralF)
            VariableF variableF ->
                return $ Variable.simplify (getConst variableF)
