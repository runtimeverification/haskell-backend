{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import qualified Control.Error as Error
import qualified Control.Exception as Exception
import           Data.Function
import           Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Step.Function.Evaluator as Evaluator
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
import           Kore.Step.Substitution
                 ( normalize )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a `TermLike`, returning a 'Pattern'.
-}
simplify
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> Simplifier (Pattern variable)
simplify patt = do
    orPatt <- simplifyToOr patt
    return (OrPattern.toPattern orPatt)

{- | The internal state of the simplification loop.

The loop is @Stable@ if the internal simplifier was the last step because the
internal simplifier is idempotent. The loop is @Unstable@ if the last step was
applying a user-defined axiom, because applying axioms creates new opportunities
for simplification.

 -}
data Stable = Stable | Unstable

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    ::  forall variable simplifier
    .   (FreshVariable variable, SortedVariable variable)
    =>  (Show variable, Unparse variable)
    =>  MonadSimplify simplifier
    =>  TermLike variable
    ->  simplifier (OrPattern variable)
simplifyToOr =
    gatherPatterns . workerAxioms Unstable . Pattern.fromTermLike
  where
    {- | Apply user-defined axioms to the 'Pattern'.

    Axioms are applied repeatedly until there are no more to apply; then the
    pattern is sent to the internal simplifier.

     -}
    workerAxioms
        :: Stable
        -> Pattern variable
        -> BranchT simplifier (Pattern variable)
    workerAxioms stable input =
        Evaluator.evaluateOnce predicate termLike
        & Error.maybeT (workerInternal stable input) (workerAxioms Unstable)
      where
        (termLike, predicate) = Pattern.splitTerm input

    {- | Apply the internal simplifier to the 'Pattern'.

    The internal simplifier is idempotent, so do not apply it if the state is
    already 'Stable'. If the state was 'Unstable', try to apply axioms after
    the internal simplifier.

     -}
    workerInternal
        :: Stable
        -> Pattern variable
        -> BranchT simplifier (Pattern variable)
    workerInternal Unstable input = do
        simplified <- simplifyPatternInternal input
        workerAxioms Stable simplified
    workerInternal Stable input =
        Exception.assert (Pattern.isNormalized input)
        $ return input

{- | Simplify a 'Pattern' using the internal simplifier.

The input 'Substitution' must be normalized. The output 'Substitution' is
normalized and the substitution is applied to the 'TermLike'.

 -}
simplifyPatternInternal
    ::  forall variable simplifier
    .   ( SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        )
    => Pattern variable
    -> BranchT simplifier (Pattern variable)
simplifyPatternInternal (Pattern.splitTerm -> (termLike, predicate)) = do
    Exception.assert (Predicate.isNormalized predicate) $ return ()
    simplified <- simplifyInternalExt predicate termLike >>= scatter
    let (termLike', predicate') = Pattern.splitTerm simplified
    predicate'' <- normalize (predicate <> predicate')
    let subst = Substitution.toMap $ Predicate.substitution predicate''
        termLike'' = substitute subst termLike'
    return $ Pattern.withCondition termLike'' predicate''

simplifyInternal
    ::  forall variable simplifier
    .   ( SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        )
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyInternal = simplifyInternalExt Predicate.top

{- | Simplify the 'TermLike' in the context of the 'Predicate'.

@simplifyInternalExt@ 'Recursive.project's one layer of the 'TermLike' and
dispatches to one of the @Kore.Step.Simplification.*@ modules, after delegating
child simplification to 'simplifyTerm'.

 -}
-- TODO (thomas.tuegel): Actually use the context during simplification.
simplifyInternalExt
    ::  forall variable simplifier
    .   ( SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -> TermLike variable
    -> simplifier (OrPattern variable)
simplifyInternalExt _ =
    simplifyInternalWorker
  where
    simplifyChildren
        :: Traversable t
        => t (TermLike variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren =
        -- Simplify the /children/ of the pattern by delegating to the
        -- 'TermSimplifier' carried by the 'MonadSimplify' constraint.
        traverse simplifyTerm

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
                Application.simplify =<< simplifyChildren applySymbolF
            CeilF ceilF ->
                Ceil.simplify =<< simplifyChildren ceilF
            EqualsF equalsF ->
                Equals.simplify =<< simplifyChildren equalsF
            ExistsF existsF ->
                Exists.simplify =<< simplifyChildren existsF
            IffF iffF ->
                Iff.simplify =<< simplifyChildren iffF
            ImpliesF impliesF ->
                Implies.simplify =<< simplifyChildren impliesF
            InF inF ->
                In.simplify =<< simplifyChildren inF
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
