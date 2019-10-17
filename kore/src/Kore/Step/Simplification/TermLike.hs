{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import qualified Control.Exception as Exception
import qualified Control.Lens.Combinators as Lens
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
import Kore.Predicate.Predicate
    ( isPredicate
    )
import qualified Kore.Profiler.Profile as Profiler
    ( identifierSimplification
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( matchAxiomIdentifier
    )
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
import qualified Kore.Substitute as Substitute
import Kore.Unparser
    ( unparse
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
    ->  Predicate variable
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
    =>  Predicate variable
    ->  TermLike variable
    ->  simplifier (OrPattern variable)
simplifyToOr term predicate =
    localSimplifierTermLike (const simplifier)
        . simplifyInternal predicate
        $ term
  where
    simplifier = termLikeSimplifier simplifyToOr

simplifyInternal
    ::  forall variable simplifier
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
        , Substitute.SubstitutionVariable variable
        , MonadSimplify simplifier
        )
    =>  TermLike variable
    ->  Predicate variable
    ->  simplifier (OrPattern variable)
simplifyInternal term predicate = simplifyInternalWorker term
  where
    tracer termLike = case AxiomIdentifier.matchAxiomIdentifier termLike of
        Nothing -> id
        Just identifier -> Profiler.identifierSimplification identifier

    predicateFreeVars =
        FreeVariables.getFreeVariables $ Predicate.freeVariables predicate

    simplifyChildren
        :: Traversable t
        => t (TermLike variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren = traverse simplifyInternalWorker

    simplifyInternalWorker termLike =
        assertTermNotPredicate . assertSimplifiedResults $ tracer termLike $
        let doNotSimplify =
                Exception.assert (TermLike.isSimplified termLike)
                return (OrPattern.fromTermLike termLike)
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
            ExistsF exists ->
                let fresh = Lens.over Binding.existsBinder refreshBinder exists
                in  Exists.simplify =<< simplifyChildren fresh
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
            ForallF forall ->
                let fresh = Lens.over Binding.forallBinder refreshBinder forall
                in  Forall.simplify <$> simplifyChildren fresh
            InhabitantF inhF -> Inhabitant.simplify <$> simplifyChildren inhF
            MuF mu ->
                let fresh = Lens.over Binding.muBinder refreshBinder mu
                in  Mu.simplify <$> simplifyChildren fresh
            NuF nu ->
                let fresh = Lens.over Binding.nuBinder refreshBinder nu
                in  Nu.simplify <$> simplifyChildren fresh
            -- TODO(virgil): Move next up through patterns.
            NextF nextF -> Next.simplify <$> simplifyChildren nextF
            OrF orF -> Or.simplify <$> simplifyChildren orF
            RewritesF rewritesF ->
                Rewrites.simplify <$> simplifyChildren rewritesF
            TopF topF -> Top.simplify <$> simplifyChildren topF
            --
            StringLiteralF stringLiteralF ->
                return $ StringLiteral.simplify (getConst stringLiteralF)
            VariableF variableF ->
                return $ Variable.simplify (getConst variableF)
      where
        assertSimplifiedResults getResults = do
            results <- getResults
            let unsimplified =
                    filter (not . TermLike.isSimplified . Pattern.term)
                    $ OrPattern.toPatterns results
            if null unsimplified
                then return results
                else (error . show . Pretty.vsep)
                    [ "Incomplete simplification!"
                    , Pretty.indent 2 "input:"
                    , Pretty.indent 4 (unparse termLike)
                    , Pretty.indent 2 "unsimplified results:"
                    , (Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> unsimplified)
                    , "Expected all patterns to be fully simplified."
                    ]

        assertTermNotPredicate getResults = do
            results <- getResults
            let
                -- The term of a result should never be any predicate other than
                -- Top or Bottom.
                hasPredicateTerm Conditional { term = term' }
                  | isTop term' || isBottom term' = False
                  | otherwise                     = isPredicate term'
                unsimplified =
                    filter hasPredicateTerm $ OrPattern.toPatterns results
            if null unsimplified
                then return results
                else (error . show . Pretty.vsep)
                    [ "Incomplete simplification!"
                    , Pretty.indent 2 "input:"
                    , Pretty.indent 4 (unparse termLike)
                    , Pretty.indent 2 "unsimplified results:"
                    , (Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> unsimplified)
                    , "Expected all predicates to be removed from the term."
                    ]

    refreshBinder
        :: Binding.Binder (UnifiedVariable variable) (TermLike variable)
        -> Binding.Binder (UnifiedVariable variable) (TermLike variable)
    refreshBinder binder@Binding.Binder { binderVariable, binderChild }
      | binderVariable `Set.member` predicateFreeVars =
        let existsFreeVars =
                FreeVariables.getFreeVariables
                $ TermLike.freeVariables binderChild
            fresh =
                fromMaybe (error "guard above ensures result <> Nothing")
                    $ refreshVariable
                        (predicateFreeVars <> existsFreeVars)
                        binderVariable
            freshChild =
                TermLike.substitute
                    (Map.singleton
                        binderVariable
                        (TermLike.mkVar fresh)
                    )
                    binderChild
        in Binding.Binder
            { binderVariable = fresh
            , binderChild = freshChild
            }
      | otherwise = binder
