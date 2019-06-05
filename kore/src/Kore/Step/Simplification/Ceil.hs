{-|
Module      : Kore.Step.Simplification.Ceil
Description : Tools for Ceil pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Ceil
    ( simplify
    , makeEvaluate
    , makeEvaluateTerm
    , simplifyEvaluated
    , Ceil (..)
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map

import qualified Kore.Attribute.Symbol as Attribute.Symbol
                 ( isTotal )
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.MultiAnd as MultiAnd
                 ( make )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Logger
                 ( LogMessage, WithLog )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import qualified Kore.Step.Function.Evaluator as Axiom
                 ( evaluatePattern )
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import qualified Kore.Step.Simplification.AndPredicates as And
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.TopBottom
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => Ceil Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify Ceil { ceilChild = child } = simplifyEvaluated child

{-| 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Ceil Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated child =
    MultiOr.flatten <$> traverse makeEvaluate child

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate child
  | Pattern.isTop    child = return (OrPattern.top)
  | Pattern.isBottom child = return (OrPattern.bottom)
  | otherwise              = makeEvaluateNonBoolCeil child

makeEvaluateNonBoolCeil
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateNonBoolCeil patt@Conditional {term}
  | isTop term = return $ OrPattern.fromPattern patt
  | otherwise = do
    termCeil <- makeEvaluateTerm term
    result <-
        And.simplifyEvaluatedMultiPredicate
            (MultiAnd.make
                [ MultiOr.make [Predicate.eraseConditionalTerm patt]
                , termCeil
                ]
            )
    return (fmap Pattern.fromPredicate result)

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a TermLike, see 'simplify' for details.
-}
-- NOTE (hs-boot): Please update Ceil.hs-boot file when changing the
-- signature.
makeEvaluateTerm
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => TermLike variable
    -> simplifier (OrPredicate variable)
makeEvaluateTerm term@(Recursive.project -> _ :< projected) = do
    tools <- Simplifier.askMetadataTools
    makeEvaluateTermWorker tools
  where
    makeEvaluateTermWorker tools
      | isTop term                = return OrPredicate.top
      | isBottom term             = return OrPredicate.bottom
      | isTotalPattern tools term = return OrPredicate.top

      | ApplicationF app <- projected
      , let Application { applicationSymbolOrAlias = patternHead } = app
      , let headAttributes = MetadataTools.symAttributes tools patternHead
      , Attribute.Symbol.isTotal headAttributes = do
            let Application { applicationChildren = children } = app
            simplifiedChildren <- mapM makeEvaluateTerm children
            let ceils = simplifiedChildren
            And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)

      | BuiltinF child <- projected = makeEvaluateBuiltin child

      | otherwise = do
            substitutionSimplifier <- Simplifier.askSimplifierPredicate
            simplifier <- Simplifier.askSimplifierTermLike
            axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
            evaluation <- Axiom.evaluatePattern
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (mkCeil_ term)
                (OrPattern.fromPattern Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate term
                    , substitution = mempty
                    }
                )
            return (fmap toPredicate evaluation)

    toPredicate Conditional {term = Top_ _, predicate, substitution} =
        Conditional {term = (), predicate, substitution}
    toPredicate patt =
        error
            (  "Ceil simplification is expected to result ai a predicate, but"
            ++ " got (" ++ show patt ++ ")."
            ++ " The most likely cases are: evaluating predicate symbols, "
            ++ " and predicate symbols are currently unrecognized as such, "
            ++ "and programming errors."
            )

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Builtin (TermLike variable)
    -> simplifier (OrPredicate variable)
makeEvaluateBuiltin
    (Domain.BuiltinMap Domain.InternalMap { builtinMapChild = m })
  = do
    children <- mapM makeEvaluateTerm values
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)
  where
    values :: [TermLike variable]
    -- Maps assume that their keys are relatively functional.
    values = Map.elems m
makeEvaluateBuiltin (Domain.BuiltinList l) = do
    children <- mapM makeEvaluateTerm (Foldable.toList l)
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)
makeEvaluateBuiltin (Domain.BuiltinSet _) =
    -- Sets assume that their elements are relatively functional.
    return OrPredicate.top
makeEvaluateBuiltin (Domain.BuiltinBool _) = return OrPredicate.top
makeEvaluateBuiltin (Domain.BuiltinInt _) = return OrPredicate.top
makeEvaluateBuiltin (Domain.BuiltinString _) = return OrPredicate.top
