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
import Data.Functor.Foldable
       ( project )
import Data.Maybe
       ( fromMaybe )
import Data.Reflection
       ( give )

import           Kore.AST.Common
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
                 ( makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, fromPurePattern )
import           Kore.Step.PatternAttributes
                 ( isConstructorLikeTop, isFunctionPattern )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )
import           Kore.Variables.Int
                 ( )

data SimplificationType = SimplifyAnd | SimplifyEquals

{-| equals for two terms. It assumes that this will be part of a predicate
which has a special condition for testing bottom=bottom equality.

This is very similar to termAnd.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.
-}
termEquals
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        (IntCounter (ExpandedPattern level Variable, SimplificationProof level))
termEquals tools first second = do  -- Maybe monad
    result <-termEqualsAnd tools first second
    return $ do  -- IntCounter monad
        (patt, _pred) <- result
        return (patt {ExpandedPattern.term = mkTop}, SimplificationProof)

termEqualsAnd
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        (IntCounter (ExpandedPattern level Variable, SimplificationProof level))
termEqualsAnd tools =
    maybeTermEquals
        tools
        (\p1 p2 -> Just $ termEqualsAndChild tools p1 p2)

termEqualsAndChild
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> IntCounter (ExpandedPattern level Variable, SimplificationProof level)
termEqualsAndChild tools first second =
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
            (\p1 p2 -> Just $ termEqualsAndChild tools p1 p2)
            first
            second
        )

maybeTermEquals
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level Variable
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        ( IntCounter (ExpandedPattern level Variable
        , SimplificationProof level)
        )
maybeTermEquals =
    maybeTransformTerm
        [ liftET equalAndEquals
        , lift   (variableFunctionAndEquals SimplifyEquals)
        , lift   (functionVariableAndEquals SimplifyEquals)
        ,        equalInjectiveHeadsAndEquals
        , liftE  sortInjectionAndEqualsAssumesDifferentHeads
        , liftE  constructorSortInjectionAndEquals
        , liftE  constructorAndEqualsAssumesDifferentHeads
        , liftET domainValueAndEqualsAssumesDifferent
        , liftET stringLiteralAndEqualsAssumesDifferent
        , liftET charLiteralAndEqualsAssumesDifferent
        ]
  where
    lift = transformerLift
    liftE = lift . toExpanded
    liftET = liftE . addToolsArg

{-| unification for two terms. Note that, most likely, we do not want
to throw away the term, since the substitution part relies on it being
non-bottom.

The main difference from 'termAnd' is that termUnification does not make an
"and" term when it does not know how to handle the given values, it returns
Nothing instead. Arguably, they should be the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.
-}
termUnification
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        (IntCounter (ExpandedPattern level Variable, SimplificationProof level))
termUnification tools =
    maybeTermAnd
        tools
        (termUnification tools)

{-| "and" simplification for two terms. The comment for
'Kore.Step.Simplification.And.simplify' describes all the special cases
handled by this.
-}
termAnd
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> IntCounter (ExpandedPattern level Variable, SimplificationProof level)
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
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level Variable
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        ( IntCounter (ExpandedPattern level Variable
        , SimplificationProof level)
        )
maybeTermAnd =
    maybeTransformTerm
        [ liftET boolAnd
        , liftET equalAndEquals
        , lift (variableFunctionAndEquals SimplifyAnd)
        , lift (functionVariableAndEquals SimplifyAnd)
        , equalInjectiveHeadsAndEquals
        , liftE sortInjectionAndEqualsAssumesDifferentHeads
        , liftE constructorSortInjectionAndEquals
        , liftE constructorAndEqualsAssumesDifferentHeads
        , liftET domainValueAndEqualsAssumesDifferent
        , liftET stringLiteralAndEqualsAssumesDifferent
        , liftET charLiteralAndEqualsAssumesDifferent
        , lift functionAnd
        ]
  where
    lift = transformerLift
    liftE = lift . toExpanded
    liftET = liftE . addToolsArg

type TermTransformation level variable =
    (  MetadataTools level StepperAttributes
    -> TermSimplifier level variable
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> FunctionResult
        (Maybe
            ( IntCounter (ExpandedPattern level variable
            , SimplificationProof level)
            )
        )
    )

maybeTransformTerm
    ::  ( MetaOrObject level
        )
    => [TermTransformation level Variable]
    -> MetadataTools level StepperAttributes
    -> TermSimplifier level Variable
    -- ^ Used to simplify subterm pairs.
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        ( IntCounter (ExpandedPattern level Variable
        , SimplificationProof level)
        )
maybeTransformTerm topTransformers tools childTransformers first second =
    firstHandledWithDefault
        Nothing
        (map (\f -> f tools childTransformers first second) topTransformers)

addToolsArg
    ::  (  PureMLPattern level Variable
        -> PureMLPattern level Variable
        -> FunctionResult
            (PureMLPattern level Variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> PureMLPattern level Variable
        -> PureMLPattern level Variable
        -> FunctionResult
            (PureMLPattern level Variable, SimplificationProof level)
        )
addToolsArg = pure

toExpanded
    :: MetaOrObject level
    =>   (  MetadataTools level StepperAttributes
        -> PureMLPattern level Variable
        -> PureMLPattern level Variable
        -> FunctionResult
            (PureMLPattern level Variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> PureMLPattern level Variable
        -> PureMLPattern level Variable
        -> FunctionResult
            (ExpandedPattern level Variable, SimplificationProof level)
        )
toExpanded transformer tools first second =
    case transformer tools first second of
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

transformerLift
    ::  (  MetadataTools level StepperAttributes
        -> PureMLPattern level Variable
        -> PureMLPattern level Variable
        -> FunctionResult
            (ExpandedPattern level Variable, SimplificationProof level)
        )
    -> TermTransformation level Variable
transformerLift
    transformation
    tools
    _childSimplifier
    first
    second
  = liftExpandedPattern (transformation tools first second)

liftExpandedPattern
    :: FunctionResult
        (ExpandedPattern level Variable, SimplificationProof level)
    -> FunctionResult
        (Maybe
            ( IntCounter
                ( ExpandedPattern level Variable
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
    :: PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
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
    ::  ( MetaOrObject level
        )
    => PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
equalAndEquals first second
  | first == second =
    Handled (first, SimplificationProof)
equalAndEquals _ _ = NotHandled

{-| And simplification for `Variable and function`.

Returns NotHandled if it could not handle the input.
-}
variableFunctionAndEquals
    ::  ( MetaOrObject level
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult
        (ExpandedPattern level Variable, SimplificationProof level)
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

{-| And simplification for `function and Variable`.

Returns NotHandled if it could not handle the input.
-}
functionVariableAndEquals
    ::  ( MetaOrObject level
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult
        (ExpandedPattern level Variable, SimplificationProof level)
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
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level Variable
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult
        (Maybe
            ( IntCounter (ExpandedPattern level Variable
            , SimplificationProof level)
            )
        )
equalInjectiveHeadsAndEquals
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
equalInjectiveHeadsAndEquals _ _ _ _ = NotHandled

{-| And simplification for patterns with sortInjection heads.

Assumes that the two heads were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
sortInjectionAndEqualsAssumesDifferentHeads
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
sortInjectionAndEqualsAssumesDifferentHeads
    tools
    (App_ firstHead [firstChild])
    (App_ secondHead [secondChild])
  | StepperAttributes.isSortInjection firstHeadAttributes
    && StepperAttributes.isSortInjection secondHeadAttributes
    && isConstructorLikeTop tools (project firstChild)
    && isConstructorLikeTop tools (project secondChild)
  =
    assert (firstHead /= secondHead) $
        -- TODO(virgil): This is copied from the unification code, but
        -- it's not obvious that this is correct.
        -- It should work for two constructors, but it may not work
        -- for domainvalue-domainvalue pairs - can't these be obtained
        -- through sort injections?
        --
        -- To give an example, if we have
        -- inj{Integer, s}(\dv{Nat}("1")) vs inj{Nat, s}(\dv{Nat}("1"))
        -- can it happen that
        -- \dv{Integer}("1") = inj{Nat, Integer}(\dv{Nat}("1"))?
        -- If yes, then the conditions above are not enough for returning
        -- bottom here.
        --
        -- For now we will assume that inj does not work like that.
        Handled (mkBottom, SimplificationProof)
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
sortInjectionAndEqualsAssumesDifferentHeads _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads vs
sortInjection heads.

Returns NotHandled if it could not handle the input.
-}
constructorSortInjectionAndEquals
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
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
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
constructorSortInjectionAndEquals _ _ _ = NotHandled

{-| And simplification for patterns with constructor heads.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
constructorAndEqualsAssumesDifferentHeads
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
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
    secondHeadAttributes = MetadataTools.symAttributes tools firstHead
constructorAndEqualsAssumesDifferentHeads _ _ _ = NotHandled

{-| And simplification for domain values.

Assumes that the two patterns were already tested for equality and were found
to be different.

Returns NotHandled if it could not handle the input.
-}
domainValueAndEqualsAssumesDifferent
    :: PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (StringLiteral_ _))
    second@(DV_ _ (StringLiteral_ _))
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
    :: PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
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
    :: PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult (PureMLPattern level Variable, SimplificationProof level)
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
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> FunctionResult
        (ExpandedPattern level Variable, SimplificationProof level)
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
