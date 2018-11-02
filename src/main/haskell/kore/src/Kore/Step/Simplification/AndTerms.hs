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
    , TermSimplifier
    , TermTransformation
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( ExceptT, MaybeT (..), fromMaybe )
import qualified Control.Error as Error
import           Control.Exception
                 ( assert )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Bifunctor as Bifunctor
import           Data.Functor.Foldable
                 ( project )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set
import           Prelude hiding
                 ( concat )

import           Kore.AST.Common
                 ( BuiltinDomain (..), PureMLPattern, Sort, SortedVariable,
                 SymbolOrAlias (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkApp, mkBottom, mkTop )
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import           Kore.IndexedModule.MetadataTools
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), erasePredicatedTerm )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), bottom, fromPurePattern, isBottom )
import           Kore.Step.PatternAttributes
                 ( isConstructorLikeTop )
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Error
                 ( UnificationError (..), UnificationOrSubstitutionError (..) )
import           Kore.Variables.Fresh

data SimplificationType = SimplifyAnd | SimplifyEquals

type TermSimplifier level variable m =
    (  PureMLPattern level variable
    -> PureMLPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)
    )

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

See also: 'termAnd'

 -}
termEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m
        (PredicateSubstitution level variable, SimplificationProof level)
termEquals tools substitutionSimplifier first second
  = do
    result <- termEqualsAnd tools substitutionSimplifier first second
    return (Bifunctor.first erasePredicatedTerm result)

termEqualsAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m
        (ExpandedPattern level variable, SimplificationProof level)
termEqualsAnd tools substitutionSimplifier =
    maybeTermEquals tools substitutionSimplifier termEqualsAndWorker
  where
    termEqualsAndWorker first second = do
        let maybeTermEqualsAndChild =
                maybeTermEquals
                    tools
                    substitutionSimplifier
                    termEqualsAndWorker
                    first
                    second
        fromMaybe equalsPredicate <$> runMaybeT maybeTermEqualsAndChild
      where
        equalsPredicate =
            give (MetadataTools.symbolOrAliasSorts tools)
                ( Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate first second
                    , substitution = []
                    }
                , SimplificationProof
                )

maybeTermEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m
        (ExpandedPattern level variable, SimplificationProof level)
maybeTermEquals =
    maybeTransformTerm
        [ liftET equalAndEquals
        , lift   bottomTermEquals
        , lift   termBottomEquals
        , lift   (variableFunctionAndEquals SimplifyEquals)
        , lift   (functionVariableAndEquals SimplifyEquals)
        ,        equalInjectiveHeadsAndEquals
        , addS   sortInjectionAndEqualsAssumesDifferentHeads
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
    addS f tools _substitutionSimplifier = f tools

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

Unlike 'termAnd', @termUnification@ does not make an @\\and@ term when a
particular case is not implemented; otherwise, the two are the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

-}
-- NOTE (hs-boot): Please update AndTerms.hs-boot file when changing the
-- signature.
termUnification
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        , unifier ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level (unifier m)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> unifier m
        (ExpandedPattern level variable, SimplificationProof level)
termUnification tools substitutionSimplifier =
    termUnificationWorker
  where
    termUnificationWorker pat1 pat2 = do
        let maybeTermUnification =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    termUnificationWorker
                    pat1
                    pat2
            unsupportedPatternsError =
                Error.throwE $ UnificationError UnsupportedPatterns
        Error.maybeT unsupportedPatternsError return $ maybeTermUnification

{- | Simplify the conjunction (@\\and@) of two terms.

The comment for 'Kore.Step.Simplification.And.simplify' describes all the
special cases
handled by this.

See also: 'termUnification'

-}
-- NOTE (hs-boot): Please update AndTerms.hs-boot file when changing the
-- signature.
termAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)
termAnd tools substitutionSimplifier =
    termAndWorker
  where
    termAndWorker first second = do
        let maybeTermAnd' =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    termAndWorker
                    first
                    second
        fromMaybe andPattern <$> runMaybeT maybeTermAnd'
      where
        andPattern =
            give (MetadataTools.symbolOrAliasSorts tools)
                ( ExpandedPattern.fromPurePattern (mkAnd first second)
                , SimplificationProof
                )

maybeTermAnd
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Ord (variable level)
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (ExpandedPattern level variable, SimplificationProof level)
maybeTermAnd =
    maybeTransformTerm
        [ liftET boolAnd
        , liftET equalAndEquals
        , lift (variableFunctionAndEquals SimplifyAnd)
        , lift (functionVariableAndEquals SimplifyAnd)
        , equalInjectiveHeadsAndEquals
        , addS sortInjectionAndEqualsAssumesDifferentHeads
        , liftE constructorSortInjectionAndEquals
        , liftE constructorAndEqualsAssumesDifferentHeads
        , Builtin.Map.unify
        , Builtin.Set.unify
        , Builtin.List.unify
        , liftE domainValueAndConstructorErrors
        , liftET domainValueAndEqualsAssumesDifferent
        , liftET stringLiteralAndEqualsAssumesDifferent
        , liftET charLiteralAndEqualsAssumesDifferent
        , lift functionAnd
        ]
  where
    lift = transformerLift
    liftE = lift . toExpanded
    liftET = liftE . addToolsArg
    addS f tools _substitutionSimplifier = f tools

{- | Construct the conjunction or unification of two terms.

Each @TermTransformation@ should represent one unification case and each
unification case should be handled by only one @TermTransformation@. If the
pattern heads do not match the case under consideration, call 'empty' to allow
another case to handle the patterns. If the pattern heads do match the
unification case, then use 'Control.Monad.Trans.lift' to wrap the implementation
of that case.

All the @TermTransformation@s and similar functions defined in this module call
'empty' unless given patterns matching their unification case.

 -}
type TermTransformation level variable m =
       MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> TermSimplifier level variable m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (ExpandedPattern level variable , SimplificationProof level)

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
    -> PredicateSubstitutionSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm pairs.
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (ExpandedPattern level variable , SimplificationProof level)
maybeTransformTerm
    topTransformers tools substitutionSimplifier childTransformers first second
  =
    foldr (<|>) empty
        (map
            (\f -> f
                tools substitutionSimplifier childTransformers first second
            )
            topTransformers
        )

addToolsArg
    ::  (  PureMLPattern level variable
        -> PureMLPattern level variable
        -> Maybe (PureMLPattern level variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> Maybe (PureMLPattern level variable, SimplificationProof level)
        )
addToolsArg = pure

toExpanded
    ::
    ( MetaOrObject level
    , SortedVariable variable
    , Show (variable level)
    , Eq (variable level)
    )
    =>   (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> Maybe (PureMLPattern level variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> Maybe (ExpandedPattern level variable, SimplificationProof level)
        )
toExpanded transformer tools first second =
    toExpanded0 <$> transformer tools first second
  where
    toExpanded0 (Bottom_ _, _proof) =
        (ExpandedPattern.bottom, SimplificationProof)
    toExpanded0 (term, _proof) =
        ( Predicated
            { term = term
            , predicate = makeTruePredicate
            , substitution = []
            }
        , SimplificationProof
        )

transformerLift
    :: MonadCounter m
    =>  (  MetadataTools level StepperAttributes
        -> PureMLPattern level variable
        -> PureMLPattern level variable
        -> Maybe (ExpandedPattern level variable, SimplificationProof level)
        )
    -> TermTransformation level variable m
transformerLift
    transformation
    tools
    _
    _childSimplifier
    first
    second
  = liftExpandedPattern (transformation tools first second)

liftExpandedPattern
    :: MonadCounter m
    => Maybe (ExpandedPattern level variable, SimplificationProof level)
    -> MaybeT m (ExpandedPattern level variable , SimplificationProof level)
liftExpandedPattern = MaybeT . return

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
boolAnd first second =
    case first of
        Bottom_ _ -> return (first, SimplificationProof)
        Top_ _ -> return (second, SimplificationProof)
        _ -> case second of
            Bottom_ _ -> return (second, SimplificationProof)
            Top_ _ -> return (first, SimplificationProof)
            _ -> empty

-- | Unify two identical ('==') patterns.
equalAndEquals
    ::  ( Eq (variable level)
        , Eq (variable Object)
        , MetaOrObject level
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
equalAndEquals first second
  | first == second =
    return (first, SimplificationProof)
equalAndEquals _ _ = empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
bottomTermEquals
    tools
    (Bottom_ _)
    second
  = case Ceil.makeEvaluateTerm tools second of
    (PredicateTrue, _proof) ->
        return (ExpandedPattern.bottom, SimplificationProof)
    (predicate, _proof) ->
        return
            ( Predicated
                { term = mkTop
                , predicate = give (MetadataTools.symbolOrAliasSorts tools) $
                    makeNotPredicate predicate
                , substitution = []
                }
            , SimplificationProof
            )
bottomTermEquals _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

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
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
termBottomEquals tools first second = bottomTermEquals tools second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

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
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
variableFunctionAndEquals
    SimplifyAnd
    _
    first@(Var_ v1)
    second@(Var_ v2)
  = return
        ( Predicated
            { term = if v2 > v1 then second else first
            , predicate = makeTruePredicate
            , substitution =
                [ if v2 > v1
                    then (v1, second)
                    else (v2, first)
                ]
            }
        , SimplificationProof
        )
variableFunctionAndEquals
    simplificationType
    tools
    (Var_ v)
    second
  | isFunctionPattern tools second =
    return
        ( Predicated
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
variableFunctionAndEquals _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

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
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
functionVariableAndEquals
    simplificationType
    tools
    first
    second
  = variableFunctionAndEquals simplificationType tools second first

{- | Unify two application patterns with equal, injective heads.

This includes constructors and sort injections.

See also: 'StepperAttributes.isInjective', 'StepperAttributes.isSortInjection',
'StepperAttributes.isConstructor'

 -}
equalInjectiveHeadsAndEquals
    ::  ( MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> TermSimplifier level variable m
    -- ^ Used to simplify subterm "and".
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (ExpandedPattern level variable, SimplificationProof level)
equalInjectiveHeadsAndEquals
    tools
    substitutionSimplifier
    termMerger
    (App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | isFirstInjective && isSecondInjective && firstHead == secondHead =
    Monad.Trans.lift $ do
        children <- Monad.zipWithM termMerger firstChildren secondChildren
        let predicates = ExpandedPattern.predicate . fst <$> children
            substitutions = ExpandedPattern.substitution . fst <$> children
        (merged, _proof) <-
            mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                predicates
                substitutions
        let PredicateSubstitution
                { predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
              =
                merged
        return
            ( Predicated
                { term = give (MetadataTools.symbolOrAliasSorts tools) $
                    mkApp firstHead (map (ExpandedPattern.term . fst) children)
                , predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
            , SimplificationProof
            )
  where
    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead

    isFirstInjective =  StepperAttributes.isInjective firstHeadAttributes
    isSecondInjective = StepperAttributes.isInjective secondHeadAttributes

equalInjectiveHeadsAndEquals _ _ _ _ _ = empty

{- | Simplify the conjunction of two sort injections.

Assumes that the two heads were already tested for equality and were found
to be different.

This simplifies cases where there is a subsort relation between the injected
sorts of the conjoined patterns, such as,

@
    \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
    ===
    \inj{src2, dst}(\inj{src1, src2}(a) ∧ b)
@

when @src1@ is a subsort of @src2@.

 -}
sortInjectionAndEqualsAssumesDifferentHeads
    ::  forall level variable m .
        ( Eq (variable Object)
        , MetaOrObject level
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level variable m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (ExpandedPattern level variable , SimplificationProof level)
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
  | isFirstSortInjection && isSecondSortInjection =
    assert (firstHead /= secondHead)
    $ assert (firstDestination == secondDestination)
    $ assert (firstConstructor == secondConstructor)
    $ case () of
        _
          | firstOrigin `isSubsortOf` secondOrigin ->
            mergeFirstIntoSecond

          | secondOrigin `isSubsortOf` firstOrigin ->
            mergeSecondIntoFirst

          | isFirstConstructorLike || isSecondConstructorLike ->
            return (ExpandedPattern.bottom, SimplificationProof)

          | Set.null sortIntersection ->
            return (ExpandedPattern.bottom, SimplificationProof)

          | otherwise ->
            (error . unlines)
                [ "Sort " ++ show firstOrigin
                , "and sort " ++ show secondOrigin
                , "have common subsort(s): " ++ show sortIntersection
                ]

  where
    subsorts = MetadataTools.subsorts tools

    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead

    isFirstSortInjection = StepperAttributes.isSortInjection firstHeadAttributes
    isSecondSortInjection = StepperAttributes.isSortInjection secondHeadAttributes

    isSubsortOf = MetadataTools.isSubsortOf tools

    isFirstConstructorLike = isConstructorLikeTop tools (project firstChild)
    isSecondConstructorLike = isConstructorLikeTop tools (project secondChild)

    {- |
        Merge the terms inside a sort injection,

        \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
        ===
        \inj{src2, dst}(\inj{src1, src2}(a) ∧ b)

        when src1 is a subsort of src2.
     -}
    mergeFirstIntoSecond
        :: MaybeT m (ExpandedPattern level variable, SimplificationProof level)
    mergeFirstIntoSecond = Monad.Trans.lift $ do
        let firstIntoSecond = sortInjection firstOrigin secondOrigin firstChild
        (merged, _) <- termMerger firstIntoSecond secondChild
        return (termSortInjection secondOrigin secondDestination merged)

    {- |
        Merge the terms inside a sort injection,

        \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
        ===
        \inj{src1, dst}(a ∧ \inj{src2, src1}(b))

        when src2 is a subsort of src1.
     -}
    mergeSecondIntoFirst
        :: MaybeT m (ExpandedPattern level variable, SimplificationProof level)
    mergeSecondIntoFirst = Monad.Trans.lift $ do
        let secondIntoFirst = sortInjection secondOrigin firstOrigin secondChild
        (merged, _) <- termMerger firstChild secondIntoFirst
        return (termSortInjection firstOrigin firstDestination merged)

    termSortInjection
        :: Sort level
        -> Sort level
        -> ExpandedPattern level variable
        -> (ExpandedPattern level variable, SimplificationProof level)
    termSortInjection
        originSort
        destinationSort
        patt
      =
        if ExpandedPattern.isBottom patt
        then (ExpandedPattern.bottom, SimplificationProof)
        else ( sortInjection originSort destinationSort <$> patt
            , SimplificationProof
            )
    sortInjection
        :: Sort level
        -> Sort level
        -> PureMLPattern level variable
        -> PureMLPattern level variable
    sortInjection originSort destinationSort term =
        give (MetadataTools.symbolOrAliasSorts tools)
            $ mkApp
                SymbolOrAlias
                    { symbolOrAliasConstructor = firstConstructor
                    , symbolOrAliasParams = [originSort, destinationSort]
                    }
                [term]
    firstSubsorts = subsorts firstOrigin
    secondSubsorts = subsorts secondOrigin
    sortIntersection = Set.intersection firstSubsorts secondSubsorts

sortInjectionAndEqualsAssumesDifferentHeads _ _ _ _ = empty

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
-- TODO (virgil): This implementation is provisional, we're not sure yet if sort
-- injection should always clash with constructors. We should clarify this.
constructorSortInjectionAndEquals
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
constructorSortInjectionAndEquals
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | isConstructorSortInjection =
    assert (firstHead /= secondHead) $
        return (mkBottom, SimplificationProof)
  where
    -- Are we asked to unify a constructor with a sort injection?
    isConstructorSortInjection =
        (||)
            (isConstructor   firstHead && isSortInjection secondHead)
            (isSortInjection firstHead && isConstructor   secondHead)
    isConstructor = give tools StepperAttributes.isConstructor_
    isSortInjection = give tools StepperAttributes.isSortInjection_
constructorSortInjectionAndEquals _ _ _ = empty

{-| Unify two constructor application patterns.

Assumes that the two patterns were already tested for equality and were found
to be different; therefore their conjunction is @\\bottom@.

 -}
constructorAndEqualsAssumesDifferentHeads
    ::  ( Eq (variable Object)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
constructorAndEqualsAssumesDifferentHeads
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | isConstructor firstHead && isConstructor secondHead =
    assert (firstHead /= secondHead) $
        return (mkBottom, SimplificationProof)
  where
    isConstructor = give tools StepperAttributes.isConstructor_
constructorAndEqualsAssumesDifferentHeads _ _ _ = empty

{- | Unify a domain value pattern with a constructor application.

This unification case throws an error because domain values may not occur in a
sort with constructors.

-}
domainValueAndConstructorErrors
    :: ( Eq (variable Object)
       , MetaOrObject level
       )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
domainValueAndConstructorErrors
    tools
    (DV_ _ _)
    (App_ secondHead _)
    | give tools StepperAttributes.isConstructor_ secondHead =
      error "Cannot handle DomainValue and Constructor"
domainValueAndConstructorErrors
    tools
    (App_ firstHead _)
    (DV_ _ _)
    | give tools StepperAttributes.isConstructor_ firstHead =
      error "Cannot handle Constructor and DomainValue"
domainValueAndConstructorErrors _ _ _ = empty

{- | Unify two domain values.

The two patterns are assumed to be inequal; therefore this case always return
@\\bottom@.

See also: 'equalAndEquals'

-}
-- TODO (thomas.tuegel): This unification case assumes that \dv is injective,
-- but it is not.
domainValueAndEqualsAssumesDifferent
    :: Eq (variable Object)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (BuiltinDomainPattern _))
    second@(DV_ _ (BuiltinDomainPattern _))
  =
    assert (first /= second) $
        return (mkBottom, SimplificationProof)
domainValueAndEqualsAssumesDifferent _ _ = empty

{-| Unify two literal strings.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
stringLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
stringLiteralAndEqualsAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  =
    assert (first /= second) $
        return (mkBottom, SimplificationProof)
stringLiteralAndEqualsAssumesDifferent _ _ = empty

{-| Unify two literal characters.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
charLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (PureMLPattern level variable, SimplificationProof level)
charLiteralAndEqualsAssumesDifferent
    first@(CharLiteral_ _)
    second@(CharLiteral_ _)
  =
    assert (first /= second) $
        return (mkBottom, SimplificationProof)
charLiteralAndEqualsAssumesDifferent _ _ = empty

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate.

-}
functionAnd
    ::  ( MetaOrObject level
        , Show (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
functionAnd
    tools
    first
    second
  | isFunctionPattern tools first && isFunctionPattern tools second =
    return
        ( Predicated
            { term = first  -- different for Equals
            -- Ceil predicate not needed since first being
            -- bottom will make the entire term bottom. However,
            -- one must be careful to not just drop the term.
            , predicate = give (MetadataTools.symbolOrAliasSorts tools) $
                makeEqualsPredicate first second
            , substitution = []
            }
        , SimplificationProof
        )
  | otherwise = empty
