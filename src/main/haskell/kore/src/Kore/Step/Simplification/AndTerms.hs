{-|
Module      : Kore.Step.Simplification.AndTerms
Description : Unification and "and" simplification for terms.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.AndTerms
    ( termAnd
    , termUnification
    ) where

import Control.Exception
       ( assert )
import Data.Maybe
       ( fromMaybe )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkApp, mkBottom )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_, pattern Bottom_, pattern CharLiteral_,
                 pattern DV_, pattern StringLiteral_, pattern Top_,
                 pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), fromPurePattern )
import           Kore.Step.PatternAttributes
                 ( isFunctionPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )
import           Kore.Variables.Int
                 ( IntVariable )

{-| unification for two terms. Note that, most likely, you do not want
to throw away the term, since the substitution part relies on it being
non-bottom.

The main difference from 'termAnd' is that termUnification does not make an
"and" term when it does not know how to handle the given values, it returns
Nothing instead. Arguably, they should be the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases that this handles.
-}
termUnification
    ::  ( MetaOrObject level
        , Hashable variable
        , IntVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (IntCounter (ExpandedPattern level variable, SimplificationProof level))
termUnification tools =
    maybeTermAnd
        tools
        (termUnification tools)

{-| "and" simplification for two terms. The comment for
'Kore.Step.Simplification.And.simplify' describes all the special cases
that this handles.
-}
termAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , IntVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> IntCounter (ExpandedPattern level variable, SimplificationProof level)
termAnd tools first second =
    fromMaybe
        (give (MetadataTools.sortTools tools) $
            return
                ( ExpandedPattern.fromPurePattern (mkAnd first second)
                , SimplificationProof
                )
        )
        (maybeTermAnd tools (\p1 p2 -> Just $ termAnd tools p1 p2) first second)

type TermSimplifier level variable =
    (  PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (IntCounter
            (ExpandedPattern level variable, SimplificationProof level)
        )
    )

data FunctionResult a
    = Handled a
    | NotHandled

maybeTermAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , IntVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level variable
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        ( IntCounter (ExpandedPattern level variable
        , SimplificationProof level)
        )
maybeTermAnd tools termMerger first second =
    firstHandledWithDefault
        Nothing
        [ liftPurePattern $
            boolAnd first second
        , liftPurePattern $
            equalAnd first second
        , liftExpandedPattern $
            variableFunctionAnd tools first second
        , liftExpandedPattern $
            -- Note that when doing actual proofs one can't just reverse the
            -- order of first and second, so this needs to be changed.
            variableFunctionAnd tools second first
        , equalInjectiveHeadsAnd tools termMerger first second
        , liftPurePattern $
            sortInjectionAndAssumesDifferentHeads tools first second
        , liftPurePattern $
            constructorSortInjectionAnd tools first second
        , liftPurePattern $
            constructorAndAssumesDifferentHeads tools first second
        , liftPurePattern $
            domainValueAndAssumesDifferent first second
        , liftPurePattern$
            stringLiteralAndAssumesDifferent first second
        , liftPurePattern $
            charLiteralAndAssumesDifferent first second
        ]
  where
    liftPurePattern
        :: MetaOrObject level
        => FunctionResult
            (PureMLPattern level variable, SimplificationProof level)
        -> FunctionResult
            ( Maybe
                ( IntCounter
                    ( ExpandedPattern level variable
                    , SimplificationProof level
                    )
                )
            )
    liftPurePattern (Handled (patt, proof)) =
        Handled $ Just $ return
            ( ExpandedPattern.fromPurePattern patt
            , proof
            )
    liftPurePattern NotHandled = NotHandled
    liftExpandedPattern
        :: FunctionResult
            (ExpandedPattern level variable, SimplificationProof level)
        -> FunctionResult
            (Maybe
                ( IntCounter
                    ( ExpandedPattern level variable
                    , SimplificationProof level
                    )
                )
            )
    liftExpandedPattern (Handled (patt, proof)) =
        Handled $ Just $ return (patt, proof)
    liftExpandedPattern NotHandled = NotHandled

firstHandledWithDefault
    :: a -> [FunctionResult a] -> a
firstHandledWithDefault default' [] = default'
firstHandledWithDefault default' (NotHandled : results) =
    firstHandledWithDefault default' results
firstHandledWithDefault _ (Handled result : _) = result


{-| And simplification when one of the terms is a bool.

Returns NotHandled if it could not handle the input.
-}
boolAnd
    :: PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
boolAnd first second =
    case first of
        Bottom_ _ -> Handled (first, SimplificationProof)
        Top_ _ -> Handled (second, SimplificationProof)
        _ -> case second of
            Bottom_ _ -> Handled (second, SimplificationProof)
            Top_ _ -> Handled (first, SimplificationProof)
            _ -> NotHandled

{-| And simplification for identical terms.

Returns NotHandled if it could not handle the input.
-}
equalAnd
    ::  ( Eq (variable level)
        , Eq (variable Object)
        , MetaOrObject level
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
equalAnd first second
  | first == second =
    Handled (first, SimplificationProof)
equalAnd _ _ = NotHandled

{-| And simplification for `variable and function`.

Returns NotHandled if it could not handle the input.
-}
variableFunctionAnd
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
variableFunctionAnd
    tools
    (Var_ v)
    second
  = case isFunctionPattern tools second of
    Left _ -> NotHandled
    Right _proof ->
        -- assumes functional implies function.
        Handled
            ( ExpandedPattern
                { term = second  -- different for Equals
                -- Ceil predicate not needed since first being bottom will make
                -- the entire term bottom. However, one must be careful to not
                -- just drop the term.
                , predicate = makeTruePredicate
                , substitution = [(v, second)]
                }
            , SimplificationProof
            )
variableFunctionAnd _ _ _ = NotHandled

{-| And simplification for patterns with identical injective heads.

This includes constructors and sort injections.

Returns NotHandled if it could not handle the input.
-}
equalInjectiveHeadsAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , IntVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level variable
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (Maybe
            ( IntCounter (ExpandedPattern level variable
            , SimplificationProof level)
            )
        )
equalInjectiveHeadsAnd
    tools
    termMerger
    (App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | StepperAttributes.isInjective firstHeadAttributes
    && StepperAttributes.isInjective secondHeadAttributes
    && firstHead == secondHead
  = Handled $ do -- Maybe monad
    intCounterChildren <- sequenceA $
        zipWith termMerger firstChildren secondChildren
    return $ do -- IntCounter monad
        children <- sequenceA intCounterChildren
        (   PredicateSubstitution
                { predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
            , _proof
            ) <- mergePredicatesAndSubstitutions
                tools
                (map (ExpandedPattern.predicate . fst) children)
                (map (ExpandedPattern.substitution . fst) children)
        return
            ( ExpandedPattern
                { term = give (MetadataTools.sortTools tools) $
                    mkApp firstHead (map (ExpandedPattern.term . fst) children)
                , predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
            , SimplificationProof
            )
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
equalInjectiveHeadsAnd _ _ _ _ = NotHandled

{-| And simplification for patterns with sortInjection heads.

Assumes that the two heads were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
sortInjectionAndAssumesDifferentHeads
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
sortInjectionAndAssumesDifferentHeads
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | StepperAttributes.isSortInjection firstHeadAttributes
    && StepperAttributes.isSortInjection secondHeadAttributes
  =
    assert (firstHead /= secondHead) $
        Handled (mkBottom, SimplificationProof)
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
sortInjectionAndAssumesDifferentHeads _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads vs
sortInjection heads.

Returns NotHandled if it could not handle the input.
-}
constructorSortInjectionAnd
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
constructorSortInjectionAnd
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | (  StepperAttributes.isConstructor firstHeadAttributes
    && StepperAttributes.isSortInjection secondHeadAttributes
    )
    ||  (  StepperAttributes.isConstructor secondHeadAttributes
        && StepperAttributes.isSortInjection firstHeadAttributes
        )
  =
    assert (firstHead /= secondHead) $
        Handled (mkBottom, SimplificationProof)
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
constructorSortInjectionAnd _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
constructorAndAssumesDifferentHeads
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
constructorAndAssumesDifferentHeads
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | StepperAttributes.isConstructor firstHeadAttributes
    && StepperAttributes.isConstructor secondHeadAttributes
  =
    assert (firstHead /= secondHead) $
        Handled (mkBottom, SimplificationProof)
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
constructorAndAssumesDifferentHeads _ _ _ = NotHandled

{-| And simplification for domain values.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
domainValueAndAssumesDifferent
    :: Eq (variable Object)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
domainValueAndAssumesDifferent
    first@(DV_ _ (StringLiteral_ _))
    second@(DV_ _ (StringLiteral_ _))
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
domainValueAndAssumesDifferent _ _ = NotHandled

{-| And simplification for string literals.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
stringLiteralAndAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
stringLiteralAndAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
stringLiteralAndAssumesDifferent _ _ = NotHandled

{-| And simplification for char literals.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
charLiteralAndAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
charLiteralAndAssumesDifferent
    first@(CharLiteral_ _)
    second@(CharLiteral_ _)
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
charLiteralAndAssumesDifferent _ _ = NotHandled
