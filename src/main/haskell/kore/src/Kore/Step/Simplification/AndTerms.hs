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
    , termEquals
    , termUnification
    ) where

import Control.Exception
       ( assert )
import Data.Maybe
       ( fromMaybe )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( BuiltinDomain (..), Sort, SortedVariable,
                 SymbolOrAlias (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkApp, mkBottom, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_, pattern Bottom_, pattern CharLiteral_,
                 pattern DV_, pattern StringLiteral_, pattern Top_,
                 pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, fromPurePattern, isBottom )
import           Kore.Step.PatternAttributes
                 ( isFunctionPattern )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( MonadPredicateSimplifier, SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

data SimplificationType = SimplifyAnd | SimplifyEquals

{-| equals for two terms. It assumes that this will be part of a predicate
which has a special condition for testing bottom=bottom equality.

This is very similar to termAnd.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.
-}
termEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (m (PredicateSubstitution level variable, SimplificationProof level))
termEquals tools predicateSimplifier first second = do  -- Maybe monad
    result <- termEqualsAnd tools predicateSimplifier first second
    return $ do  -- Counter monad
        (ExpandedPattern {predicate, substitution}, _pred) <- result
        return
            ( PredicateSubstitution
                {predicate = predicate, substitution = substitution}
            , SimplificationProof
            )

termEqualsAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (m (ExpandedPattern level variable, SimplificationProof level))
termEqualsAnd tools predicateSimplifier =
    maybeTermEquals
        tools
        predicateSimplifier
        (\p1 p2 -> Just $ termEqualsAndChild tools predicateSimplifier p1 p2)

termEqualsAndChild
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)
termEqualsAndChild tools predicateSimplifier first second =
    fromMaybe
        (give (MetadataTools.sortTools tools) $
            return
                ( ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate first second
                    , substitution = []
                    }
                , SimplificationProof
                )
        )
        (maybeTermEquals
            tools
            predicateSimplifier
            (\p1 p2 ->
                Just $ termEqualsAndChild tools predicateSimplifier p1 p2)
            first
            second
        )

maybeTermEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        ( m (ExpandedPattern level variable, SimplificationProof level) )
maybeTermEquals =
    maybeTransformTerm
        [ liftPPtP equalAndEquals
        , liftTPPtE   bottomTermEquals
        , liftTPPtE   termBottomEquals
        , liftTPPtE   (variableFunctionAndEquals SimplifyEquals)
        , liftTPPtE   (functionVariableAndEquals SimplifyEquals)
        ,        equalInjectiveHeadsAndEquals
        , liftTTPPtPM sortInjectionAndEqualsAssumesDifferentHeads
        , liftTPPtP  constructorSortInjectionAndEquals
        , liftTPPtP  constructorAndEqualsAssumesDifferentHeads
        , liftPPtP domainValueAndEqualsAssumesDifferent
        , liftPPtP stringLiteralAndEqualsAssumesDifferent
        , liftPPtP charLiteralAndEqualsAssumesDifferent
        ]

{-| unification for two terms. Note that, most likely, we do not want
to throw away the term, since the substitution part relies on it being
non-bottom.

The main difference from 'termAnd' is that termUnification does not make an
"and" term when it does not know how to handle the given values, it returns
Nothing instead. Arguably, they should be the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

hs-boot: Please remember to update the hs-boot file when changing the signature.
-}
termUnification
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (m (ExpandedPattern level variable, SimplificationProof level))
termUnification tools predicateSimplifier =
    maybeTermAnd
        tools
        predicateSimplifier
        (termUnification tools predicateSimplifier)

{-| "and" simplification for two terms. The comment for
'Kore.Step.Simplification.And.simplify' describes all the special cases
handled by this.

hs-boot: Please remember to update the hs-boot file when changing the signature.
-}
termAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)
termAnd tools predicateSimplifier first second =
    fromMaybe
        (give (MetadataTools.sortTools tools) $
            return
                ( ExpandedPattern.fromPurePattern (mkAnd first second)
                , SimplificationProof
                )
        )
        (maybeTermAnd
            tools
            predicateSimplifier
            (\p1 p2 -> Just $ termAnd tools predicateSimplifier p1 p2)
            first
            second
        )

type TermSimplifier level variable m =
    (  PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        ( m
            (ExpandedPattern level variable, SimplificationProof level)
        )
    )

data FunctionResult a
    = Handled a
    | NotHandled

maybeTermAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (m (ExpandedPattern level variable, SimplificationProof level))
maybeTermAnd =
    maybeTransformTerm
        [ liftPPtP boolAnd
        , liftPPtP equalAndEquals
        , liftTPPtE (variableFunctionAndEquals SimplifyAnd)
        , liftTPPtE (functionVariableAndEquals SimplifyAnd)
        , equalInjectiveHeadsAndEquals
        , liftTTPPtPM sortInjectionAndEqualsAssumesDifferentHeads
        , liftTPPtP constructorSortInjectionAndEquals
        , liftTPPtP constructorAndEqualsAssumesDifferentHeads
        , liftTPPtP domainValueAndConstructorErrors
        , liftPPtP domainValueAndEqualsAssumesDifferent
        , liftPPtP stringLiteralAndEqualsAssumesDifferent
        , liftPPtP charLiteralAndEqualsAssumesDifferent
        , liftTPPtE functionAnd
        ]

type TermTransformation level variable m =
    (  MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> TermSimplifier level variable m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (Maybe
            ( m
                ( ExpandedPattern level variable
                , SimplificationProof level
                )
            )
        )
    )

maybeTransformTerm
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => [TermTransformation level variable m]
    -> MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm pairs.
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        ( m (ExpandedPattern level variable
        , SimplificationProof level)
        )
maybeTransformTerm
    topTransformers tools predicateSimplifier childTransformers first second
  =
    firstHandledWithDefault
        Nothing
        (map
            (\f -> f tools predicateSimplifier childTransformers first second)
            topTransformers
        )

liftExpandedPattern
    :: MonadCounter m
    => FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
    -> FunctionResult
        (Maybe
            ( m
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

toExpanded
    :: MetaOrObject level
    => FunctionResult (PureMLPattern level variable, SimplificationProof level)
    -> FunctionResult
        ( ExpandedPattern level variable
        , SimplificationProof level
        )
toExpanded result =
    case result of
        NotHandled -> NotHandled
        Handled (Bottom_ _, _proof) ->
            Handled (ExpandedPattern.bottom, SimplificationProof)
        Handled (term, _proof) ->
            Handled
                ( ExpandedPattern
                    { term = term
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , SimplificationProof
                )

liftTTPPtPM
    ::  (  MetadataTools level StepperAttributes
        -> TermSimplifier level variable m
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> FunctionResult
            (Maybe
                ( m
                    ( ExpandedPattern level variable
                    , SimplificationProof level
                    )
                )
            )
        )
    -> TermTransformation level variable m
liftTTPPtPM f tools _patternSimplifier =
    f tools

liftTPPtE
    :: MonadCounter m
    =>  (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> FunctionResult
            ( ExpandedPattern level variable, SimplificationProof level)
        )
    -> TermTransformation level variable m
liftTPPtE f tools _patternSimplifier _termSimplifier first second =
    liftExpandedPattern $ f tools first second

liftTPPtP
    ::  ( MetaOrObject level
        , MonadCounter m
        )
    =>  (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> FunctionResult
            ( PureMLPattern level variable, SimplificationProof level)
        )
    -> TermTransformation level variable m
liftTPPtP f tools _patternSimplifier _termSimplifier first second =
    liftExpandedPattern $ toExpanded $ f tools first second

liftPPtP
    ::  ( MetaOrObject level
        , MonadCounter m
        )
    =>  (  PureMLPattern level variable
        -> PureMLPattern level variable
        -> FunctionResult
            ( PureMLPattern level variable, SimplificationProof level)
        )
    -> TermTransformation level variable m
liftPPtP f _tools _patternSimplifier _termSimplifier first second =
    liftExpandedPattern $ toExpanded $ f first second

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
equalAndEquals
    ::  ( Eq (variable level)
        , Eq (variable Object)
        , MetaOrObject level
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
equalAndEquals first second
  | first == second =
    Handled (first, SimplificationProof)
equalAndEquals _ _ = NotHandled

{-| Equals simplification for `bottom == term`.

Returns NotHandled if it could not handle the input.
-}
bottomTermEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
bottomTermEquals
    tools
    (Bottom_ _)
    second
  = case Ceil.makeEvaluateTerm tools second of
    (PredicateTrue, _proof) ->
        Handled (ExpandedPattern.bottom, SimplificationProof)
    (predicate, _proof) ->
        Handled
            ( ExpandedPattern
                { term = mkTop
                , predicate = give (MetadataTools.sortTools tools) $
                    case makeNotPredicate predicate of
                        (predicate', _proof) -> predicate'
                , substitution = []
                }
            , SimplificationProof
            )
bottomTermEquals _ _ _ = NotHandled

{-| Equals simplification for `term == bottom`.

Returns NotHandled if it could not handle the input.
-}
termBottomEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
termBottomEquals tools first second = bottomTermEquals tools second first

{-| And simplification for `variable and function`.

Returns NotHandled if it could not handle the input.
-}
variableFunctionAndEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
variableFunctionAndEquals
    simplificationType
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
                , predicate =
                    case simplificationType of
                        -- Ceil predicate not needed since 'second' being bottom
                        -- will make the entire term bottom. However, one must
                        -- be careful to not just drop the term.
                        SimplifyAnd ->
                            makeTruePredicate
                        SimplifyEquals ->
                            case Ceil.makeEvaluateTerm tools second of
                                (pred', _proof) -> pred'
                , substitution = [(v, second)]
                }
            , SimplificationProof
            )
variableFunctionAndEquals _ _ _ _ = NotHandled

{-| And simplification for `function and variable`.

Returns NotHandled if it could not handle the input.
-}
functionVariableAndEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
functionVariableAndEquals
    simplificationType
    tools
    first
    second
  = variableFunctionAndEquals simplificationType tools second first

{-| And simplification for patterns with identical injective heads.

This includes constructors and sort injections.

Returns NotHandled if it could not handle the input.
-}
equalInjectiveHeadsAndEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> MonadPredicateSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (Maybe
            ( m
                ( ExpandedPattern level variable
                , SimplificationProof level
                )
            )
        )
equalInjectiveHeadsAndEquals
    tools
    predicateSimplifier
    termMerger
    (App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | StepperAttributes.isInjective firstHeadAttributes
    && StepperAttributes.isInjective secondHeadAttributes
    && firstHead == secondHead
  = Handled $ do -- Maybe monad
    intCounterChildren <- sequenceA $
        zipWith termMerger firstChildren secondChildren
    return $ do -- Counter monad
        children <- sequenceA intCounterChildren
        (   PredicateSubstitution
                { predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
            , _proof
            ) <- mergePredicatesAndSubstitutions
                tools
                predicateSimplifier
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
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead
equalInjectiveHeadsAndEquals _ _ _ _ _ = NotHandled

{-| And simplification for patterns with sortInjection heads.

Assumes that the two heads were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
sortInjectionAndEqualsAssumesDifferentHeads
    ::  forall level variable m.
        ( Eq (variable Object)
        , MetaOrObject level
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level variable m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (Maybe
            ( m
                ( ExpandedPattern level variable
                , SimplificationProof level
                )
            )
        )
sortInjectionAndEqualsAssumesDifferentHeads
    tools
    termMerger
    (App_
        firstHead@SymbolOrAlias
            { symbolOrAliasConstructor = firstConstructor
            , symbolOrAliasParams = [firstOrigin, firstDestination]
            }
        [firstChild])
    (App_
        secondHead@SymbolOrAlias
            { symbolOrAliasConstructor = secondConstructor
            , symbolOrAliasParams = [secondOrigin, secondDestination]
            }
        [secondChild]
    )
  | StepperAttributes.isSortInjection firstHeadAttributes
    && StepperAttributes.isSortInjection secondHeadAttributes
  =
    assert (firstHead /= secondHead)
    $ assert (firstDestination == secondDestination)
    $ assert (firstConstructor == secondConstructor)
    $ if firstOrigin `isSubsortOf` secondOrigin
        then Handled $ do  -- Maybe monad
            merged <-
                termMerger
                    (sortInjection firstOrigin secondOrigin firstChild)
                    secondChild
            return $ do  -- Counter monad
                (patt, _proof) <- merged
                let
                    (result, _proof) =
                        termSortInjection secondOrigin secondDestination patt
                return (result, SimplificationProof)
        else if secondOrigin `isSubsortOf` firstOrigin
            then Handled $ do  -- Maybe monad
                merged <-
                    termMerger
                        firstChild
                        (sortInjection secondOrigin firstOrigin secondChild)
                return $ do  -- Counter monad
                    (patt, _proof) <- merged
                    let
                        (result, _proof) =
                            termSortInjection firstOrigin firstDestination patt
                    return (result, SimplificationProof)
            else
                NotHandled
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead
    isSubsortOf = MetadataTools.isSubsortOf tools
    termSortInjection
        :: Sort level
        -> Sort level
        -> ExpandedPattern level variable
        -> (ExpandedPattern level variable, SimplificationProof level)
    termSortInjection
        originSort
        destinationSort
        patt@ExpandedPattern
            {term, predicate, substitution}
      =
        if ExpandedPattern.isBottom patt
        then (ExpandedPattern.bottom, SimplificationProof)
        else
            ( ExpandedPattern
                { term = sortInjection originSort destinationSort term
                , predicate = predicate
                , substitution = substitution
                }
            , SimplificationProof
            )
    sortInjection
        :: Sort level
        -> Sort level
        -> PureMLPattern level variable
        -> PureMLPattern level variable
    sortInjection originSort destinationSort term =
        give (MetadataTools.sortTools tools)
            $ mkApp
                SymbolOrAlias
                    { symbolOrAliasConstructor = firstConstructor
                    , symbolOrAliasParams = [originSort, destinationSort]
                    }
                [term]

sortInjectionAndEqualsAssumesDifferentHeads _ _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads vs
sortInjection heads.

Returns NotHandled if it could not handle the input.

TODO(virgil): This implementation is provisional, we're not sure yet if sort
    injection should always clash with constructors. We should clarify this.
-}
constructorSortInjectionAndEquals
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
constructorSortInjectionAndEquals
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
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead
constructorSortInjectionAndEquals _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
constructorAndEqualsAssumesDifferentHeads
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
constructorAndEqualsAssumesDifferentHeads
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
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead
constructorAndEqualsAssumesDifferentHeads _ _ _ = NotHandled

{-| And simplification for domain values and constructors.

Currently throws an error.

Returns NotHandled if the arguments are not a domain value and a constructor.
-}
domainValueAndConstructorErrors
    :: ( Eq (variable Object)
       , MetaOrObject level
       )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
domainValueAndConstructorErrors
    tools
    (DV_ _ _)
    (App_ secondHead _)
    | StepperAttributes.isConstructor
        (MetadataTools.symAttributes tools secondHead)
    = error "Cannot handle DomainValue and Constructor"
domainValueAndConstructorErrors
    tools
    (App_ firstHead _)
    (DV_ _ _)
    | StepperAttributes.isConstructor
        (MetadataTools.symAttributes tools firstHead)
    = error "Cannot handle DomainValue and Constructor"
domainValueAndConstructorErrors _ _ _ = NotHandled

{-| And simplification for domain values.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
domainValueAndEqualsAssumesDifferent
    :: Eq (variable Object)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (BuiltinDomainPattern _))
    second@(DV_ _ (BuiltinDomainPattern _))
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
domainValueAndEqualsAssumesDifferent _ _ = NotHandled

{-| And simplification for string literals.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
stringLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
stringLiteralAndEqualsAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
stringLiteralAndEqualsAssumesDifferent _ _ = NotHandled

{-| And simplification for char literals.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
charLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult (PureMLPattern level variable, SimplificationProof level)
charLiteralAndEqualsAssumesDifferent
    first@(CharLiteral_ _)
    second@(CharLiteral_ _)
  =
    assert (first /= second) $
        Handled (mkBottom, SimplificationProof)
charLiteralAndEqualsAssumesDifferent _ _ = NotHandled

{-| And simplification for `function and function`.

Returns NotHandled if it could not handle the input.
-}
functionAnd
    ::  ( MetaOrObject level
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (ExpandedPattern level variable, SimplificationProof level)
functionAnd
    tools
    first
    second
  = case isFunctionPattern tools first of
    Left _ -> NotHandled
    Right _proof ->
        case isFunctionPattern tools second of
            Left _ -> NotHandled
            Right _proof ->
                Handled
                    ( ExpandedPattern
                        { term = first  -- different for Equals
                        -- Ceil predicate not needed since first being
                        -- bottom will make the entire term bottom. However,
                        -- one must be careful to not just drop the term.
                        , predicate = give (MetadataTools.sortTools tools) $
                            makeEqualsPredicate first second
                        , substitution = []
                        }
                    , SimplificationProof
                    )
