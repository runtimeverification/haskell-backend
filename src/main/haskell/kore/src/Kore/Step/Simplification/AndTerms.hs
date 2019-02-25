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
    ( simplifySortInjections
    , termAnd
    , termEquals
    , termUnification
    , SortInjectionMatch (..)
    , SortInjectionSimplification (..)
    , TermSimplifier
    , TermTransformationOld
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( ExceptT (..), MaybeT (..), fromMaybe )
import qualified Control.Error as Error
import           Control.Exception
                 ( assert )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Functor.Foldable as Recursive
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set
import           Prelude hiding
                 ( concat )

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), erasePredicatedTerm )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), bottom, bottomPredicate, fromPurePattern,
                 isBottom, toPredicate, top, topPredicate )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toPredicate )
import           Kore.Step.Pattern
import           Kore.Step.PatternAttributes
                 ( isConstructorLikeTop )
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 SimplificationType )
import qualified Kore.Step.Simplification.Data as SimplificationType
                 ( SimplificationType (..) )
import           Kore.Step.StepperAttributes
                 ( SortInjection (..), StepperAttributes (..) )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Step.Substitution
                 ( PredicateSubstitutionMerger (PredicateSubstitutionMerger),
                 createLiftedPredicatesAndSubstitutionsMerger,
                 createPredicatesAndSubstitutionsMergerExcept )
import           Kore.Unification.Error
                 ( UnificationError (..), UnificationOrSubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh

data SimplificationTarget = AndT | EqualsT | BothT

type TermSimplifier level variable m =
    (  StepPattern level variable
    -> StepPattern level variable
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
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT m
        (OrOfPredicateSubstitution level variable, SimplificationProof level)
termEquals tools substitutionSimplifier first second = do
    (result, proof) <- termEqualsAnd tools substitutionSimplifier first second
    return (OrOfExpandedPattern.make [erasePredicatedTerm result], proof)

termEqualsAnd
    :: forall level variable m .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT m
        (ExpandedPattern level variable, SimplificationProof level)
termEqualsAnd tools substitutionSimplifier p1 p2 =
    MaybeT $ do
        eitherMaybeResult <- Error.runExceptT $ runMaybeT $
            maybeTermEquals
                tools
                substitutionSimplifier
                (createPredicatesAndSubstitutionsMergerExcept
                    tools substitutionSimplifier
                )
                termEqualsAndWorker
                p1
                p2
        return $
            case eitherMaybeResult of
                Left _ -> Nothing
                Right result -> result
  where
    termEqualsAndWorker
        :: err ~ ExceptT (UnificationOrSubstitutionError level variable)
        => StepPattern level variable
        -> StepPattern level variable
        -> (err m) (ExpandedPattern level variable, SimplificationProof level)
    termEqualsAndWorker first second = ExceptT $ do
        eitherMaybeTermEqualsAndChild <- Error.runExceptT $ runMaybeT $
            maybeTermEquals
                tools
                substitutionSimplifier
                (createPredicatesAndSubstitutionsMergerExcept
                    tools substitutionSimplifier
                )
                termEqualsAndWorker
                first
                second
        return $ Right
            (case eitherMaybeTermEqualsAndChild of
                Left _ -> equalsPredicate
                Right maybeResult ->
                    fromMaybe equalsPredicate maybeResult
            )
      where
        equalsPredicate =
            ( Predicated
                { term = mkTop_
                , predicate = makeEqualsPredicate first second
                , substitution = mempty
                }
            , SimplificationProof
            )

maybeTermEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger level variable (err m)
    -> TermSimplifier level variable (err m)
    -- ^ Used to simplify subterm "and".
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT (err m)
        (ExpandedPattern level variable, SimplificationProof level)
maybeTermEquals = maybeTransformTerm equalsFunctions

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
    :: forall level variable m err .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> err m
        (ExpandedPattern level variable, SimplificationProof level)
termUnification tools substitutionSimplifier =
    termUnificationWorker
  where
    termUnificationWorker
        :: StepPattern level variable
        -> StepPattern level variable
        -> (err m) (ExpandedPattern level variable, SimplificationProof level)
    termUnificationWorker pat1 pat2 = do
        let maybeTermUnification =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    (createPredicatesAndSubstitutionsMergerExcept
                        tools substitutionSimplifier
                    )
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
    :: forall level variable m .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> m (ExpandedPattern level variable, SimplificationProof level)
termAnd tools substitutionSimplifier p1 p2 = do
    eitherResult <- Error.runExceptT $
        termAndWorker p1 p2
    case eitherResult of
        Left _ -> return
            ( ExpandedPattern.fromPurePattern (mkAnd p1 p2)
            , SimplificationProof
            )
        Right result -> return result
  where
    termAndWorker
        :: (err ~ ExceptT (UnificationOrSubstitutionError level variable))
        => StepPattern level variable
        -> StepPattern level variable
        -> (err m) (ExpandedPattern level variable, SimplificationProof level)
    termAndWorker first second = do
        let maybeTermAnd' =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    (createLiftedPredicatesAndSubstitutionsMerger
                        tools substitutionSimplifier
                    )
                    termAndWorker
                    first
                    second
        fromMaybe andPattern <$> runMaybeT maybeTermAnd'
      where
        andPattern =
                ( ExpandedPattern.fromPurePattern (mkAnd first second)
                , SimplificationProof
                )

maybeTermAnd
    ::  ( MetaOrObject level
        , FreshVariable variable
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , SortedVariable variable
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger level variable (err m)
    -> TermSimplifier level variable (err m)
    -- ^ Used to simplify subterm "and".
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable, SimplificationProof level)
maybeTermAnd = maybeTransformTerm andFunctions

andFunctions
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Monad m
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        )
    => [TermTransformationOld level variable m]
andFunctions =
    map (forAnd . snd) (filter appliesToAnd andEqualsFunctions)
  where
    appliesToAnd :: (SimplificationTarget, a) -> Bool
    appliesToAnd (AndT, _) = True
    appliesToAnd (EqualsT, _) = False
    appliesToAnd (BothT, _) = True

    forAnd
        :: TermTransformation level variable m
        -> TermTransformationOld level variable m
    forAnd f = f SimplificationType.And

equalsFunctions
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Monad m
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        )
    => [TermTransformationOld level variable m]
equalsFunctions =
    map (forEquals . snd) (filter appliesToEquals andEqualsFunctions)
  where
    appliesToEquals :: (SimplificationTarget, a) -> Bool
    appliesToEquals (AndT, _) = False
    appliesToEquals (EqualsT, _) = True
    appliesToEquals (BothT, _) = True

    forEquals
        :: TermTransformation level variable m
        -> TermTransformationOld level variable m
    forEquals f = f SimplificationType.Equals

andEqualsFunctions
    :: forall variable level m err .
        ( Eq (variable level)
        , FreshVariable variable
        , MetaOrObject level
        , Monad m
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => [(SimplificationTarget, TermTransformation level variable m)]
andEqualsFunctions =
    [ (AndT,    liftET boolAnd)
    , (BothT,   liftET equalAndEquals)
    , (EqualsT, lift0  bottomTermEquals)
    , (EqualsT, lift0  termBottomEquals)
    , (BothT,   liftTS variableFunctionAndEquals)
    , (BothT,   liftTS functionVariableAndEquals)
    , (BothT,   addT   equalInjectiveHeadsAndEquals)
    , (BothT,   addS   sortInjectionAndEqualsAssumesDifferentHeads)
    , (BothT,   liftE  constructorSortInjectionAndEquals)
    , (BothT,   liftE  constructorAndEqualsAssumesDifferentHeads)
    , (BothT,   liftB  Builtin.Map.unifyEquals)
    , (BothT,   liftB  Builtin.Set.unifyEquals)
    , (BothT,   liftB  Builtin.List.unifyEquals)
    , (BothT,   liftE  domainValueAndConstructorErrors)
    , (BothT,   liftET domainValueAndEqualsAssumesDifferent)
    , (BothT,   liftET stringLiteralAndEqualsAssumesDifferent)
    , (BothT,   liftET charLiteralAndEqualsAssumesDifferent)
    , (AndT,    lift   functionAnd)
    ]
  where
    liftB
        f
        simplificationType
        tools
        substitutionSimplifier
        _substitutionMerger
      = f simplificationType tools substitutionSimplifier

    lift = pure . transformerLiftOld
    liftE = lift . toExpanded
    liftET = liftE . addToolsArg
    addS f _simplificationType tools _substitutionSimplifier _substitutionMerger
      = f tools
    addT
        ::  (  MetadataTools level StepperAttributes
            -> PredicateSubstitutionMerger level variable (err m)
            -> TermSimplifier level variable (err m)
            -> StepPattern level variable
            -> StepPattern level variable
            -> MaybeT (err m)
                (ExpandedPattern level variable , SimplificationProof level)
            )
        -> TermTransformation level variable m
    addT f _simplificationType tools _substitutionSimplifier =
        f tools
    lift0
        f
        _simplificationType
        tools
        substitutionSimplifier
        _substitutionMerger
        _termSimplifier
        p1
        p2
      = MaybeT $ Monad.Trans.lift $ runMaybeT $
        f tools substitutionSimplifier p1 p2
    liftTS
        f
        simplificationType
        tools
        substitutionSimplifier
        substitutionMerger
        _termSimplifier
      =
        f simplificationType tools substitutionSimplifier substitutionMerger


{- | Construct the conjunction or unification of two terms.

Each @TermTransformationOld@ should represent one unification case and each
unification case should be handled by only one @TermTransformationOld@. If the
pattern heads do not match the case under consideration, call 'empty' to allow
another case to handle the patterns. If the pattern heads do match the
unification case, then use 'Control.Monad.Trans.lift' to wrap the implementation
of that case.

All the @TermTransformationOld@s and similar functions defined in this module call
'empty' unless given patterns matching their unification case.

 -}
type TermTransformation level variable m =
       SimplificationType
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger
        level
        variable
        (ExceptT (UnificationOrSubstitutionError level variable) m)
    -> TermSimplifier
        level
        variable
        (ExceptT (UnificationOrSubstitutionError level variable) m)
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (ExceptT (UnificationOrSubstitutionError level variable) m)
        (ExpandedPattern level variable , SimplificationProof level)
type TermTransformationOld level variable m =
       MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger
        level
        variable
        (ExceptT (UnificationOrSubstitutionError level variable) m)
    -> TermSimplifier
        level
        variable
        (ExceptT (UnificationOrSubstitutionError level variable) m)
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (ExceptT (UnificationOrSubstitutionError level variable) m)
        (ExpandedPattern level variable , SimplificationProof level)

maybeTransformTerm
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , SortedVariable variable
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => [TermTransformationOld level variable m]
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger level variable (err m)
    -> TermSimplifier level variable (err m)
    -- ^ Used to simplify subterm pairs.
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable , SimplificationProof level)
maybeTransformTerm
    topTransformers
    mergeException
    tools
    substitutionSimplifier
    childTransformers
    first
    second
  =
    foldr (<|>) empty
        (map
            (\f -> f
                mergeException
                tools
                substitutionSimplifier
                childTransformers
                first
                second
            )
            topTransformers
        )

addToolsArg
    ::  (  StepPattern level variable
        -> StepPattern level variable
        -> Maybe (StepPattern level variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> StepPattern level variable
        -> StepPattern level variable
        -> Maybe (StepPattern level variable, SimplificationProof level)
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
        -> StepPattern level variable
        -> StepPattern level variable
        -> Maybe (StepPattern level variable, SimplificationProof level)
        )
    ->  (  MetadataTools level StepperAttributes
        -> StepPattern level variable
        -> StepPattern level variable
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
            , substitution = mempty
            }
        , SimplificationProof
        )

transformerLiftOld
  :: Monad m
  =>  (  MetadataTools level StepperAttributes
      -> StepPattern level variable
      -> StepPattern level variable
      -> Maybe (ExpandedPattern level variable, SimplificationProof level)
      )
  -> TermTransformationOld level variable m
transformerLiftOld
    transformation
    tools
    _substitutionSimplifier
    _substitutionMerger
    _childSimplifier
    first
    second
  = liftExpandedPattern (transformation tools first second)

liftExpandedPattern
    :: Monad m
    => Maybe (ExpandedPattern level variable, SimplificationProof level)
    -> MaybeT m (ExpandedPattern level variable , SimplificationProof level)
liftExpandedPattern = MaybeT . return

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
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
    => StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
equalAndEquals first second
  | first == second =
    return (first, SimplificationProof)
equalAndEquals _ _ = empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT m (ExpandedPattern level variable, SimplificationProof level)
bottomTermEquals
    tools
    substitutionSimplifier
    (Bottom_ _)
    second
  = Monad.Trans.lift $ do
    (secondCeil, _proof) <-
        Ceil.makeEvaluateTerm tools substitutionSimplifier second
    case OrOfExpandedPattern.extractPatterns secondCeil of
        [] -> return (ExpandedPattern.top, SimplificationProof)
        [ Predicated
            {term = (), predicate = PredicateTrue, substitution}
          ]
          | substitution == mempty ->
            return (ExpandedPattern.bottom, SimplificationProof)
        _ -> return
            ( Predicated
                { term = mkTop_
                , predicate =
                    makeNotPredicate
                        (OrOfExpandedPattern.toPredicate
                            (fmap ExpandedPattern.toPredicate secondCeil)
                        )
                , substitution = mempty
                }
            , SimplificationProof
            )
bottomTermEquals _ _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT m (ExpandedPattern level variable, SimplificationProof level)
termBottomEquals tools substitutionSimplifier first second =
    bottomTermEquals tools substitutionSimplifier second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionAndEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger level variable (err m)
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable, SimplificationProof level)
variableFunctionAndEquals
    SimplificationType.And
    _tools
    _substitutionSimplifier
    _substitutionMerger
    first@(Var_ v1)
    second@(Var_ v2)
  = return
        ( Predicated
            { term = if v2 > v1 then second else first
            , predicate = makeTruePredicate
            , substitution = Substitution.wrap
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
    substitutionSimplifier
    (PredicateSubstitutionMerger substitutionMerger)
    (Var_ v)
    second
  | isFunctionPattern tools second = Monad.Trans.lift $ do -- ExceptT Simplifier
    Predicated {term = (), predicate, substitution} <- Monad.Trans.lift $
        case simplificationType of -- Simplifier
            SimplificationType.And ->
                -- Ceil predicate not needed since 'second' being bottom
                -- will make the entire term bottom. However, one must
                -- be careful to not just drop the term.
                return ExpandedPattern.topPredicate
            SimplificationType.Equals -> do
                (resultOr, _proof) <-
                    Ceil.makeEvaluateTerm tools substitutionSimplifier second
                case OrOfExpandedPattern.extractPatterns resultOr of
                    [] -> return ExpandedPattern.bottomPredicate
                    [resultPredicateSubstitution] ->
                        return resultPredicateSubstitution
                    _ -> error
                        (  "Unimplemented, ceil of "
                        ++ show second
                        ++ " returned multiple results: "
                        ++ show resultOr
                        ++ ". This could happen, as an example, when"
                        ++ " defining ceil(f(x))=g(x), and the evaluation for"
                        ++ " g(x) splits the configuration."
                        )
    Predicated
        { term = ()
        , predicate = resultPredicate
        , substitution = resultSubstitution
        } <- substitutionMerger
            [predicate]
            [substitution, Substitution.wrap [(v, second)]]
    return
        ( Predicated
            { term = second  -- different for Equals
            , predicate = resultPredicate
            , substitution = resultSubstitution
            }
        , SimplificationProof
        )
variableFunctionAndEquals _ _ _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

 -}
functionVariableAndEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => SimplificationType
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionMerger level variable (err m)
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable, SimplificationProof level)
functionVariableAndEquals
    simplificationType
    tools
    substitutionSimplifier
    substitutionMerger
    first
    second
  =
    variableFunctionAndEquals
        simplificationType
        tools
        substitutionSimplifier
        substitutionMerger
        second
        first

{- | Unify two application patterns with equal, injective heads.

This includes constructors and sort injections.

See also: 'StepperAttributes.isInjective', 'StepperAttributes.isSortInjection',
'StepperAttributes.isConstructor'

 -}
equalInjectiveHeadsAndEquals
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionMerger level variable (err m)
    -> TermSimplifier level variable (err m)
    -- ^ Used to simplify subterm "and".
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable, SimplificationProof level)
equalInjectiveHeadsAndEquals
    tools
    (PredicateSubstitutionMerger substitutionMerger)
    termMerger
    firstPattern@(App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | isFirstInjective && isSecondInjective && firstHead == secondHead =
    Monad.Trans.lift $ do
        children <- Monad.zipWithM termMerger firstChildren secondChildren
        let predicates = ExpandedPattern.predicate . fst <$> children
            substitutions = ExpandedPattern.substitution . fst <$> children
        Predicated
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            } <- substitutionMerger predicates substitutions
        return
            ( Predicated
                { term =
                    mkApp
                        (getSort firstPattern)
                        firstHead
                        (ExpandedPattern.term . fst <$> children)
                , predicate = mergedPredicate
                , substitution = mergedSubstitution
                }
            , SimplificationProof
            )
  where
    isFirstInjective = give tools StepperAttributes.isInjective_ firstHead
    isSecondInjective = give tools StepperAttributes.isInjective_ secondHead

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
    ::  forall level variable m err .
        ( Ord (variable level)
        , MetaOrObject level
        , Monad m
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> TermSimplifier level variable (err m)
    -> StepPattern level variable
    -> StepPattern level variable
    -> MaybeT
        (err m)
        (ExpandedPattern level variable, SimplificationProof level)
sortInjectionAndEqualsAssumesDifferentHeads
    tools
    termMerger
    first
    second
  = case simplifySortInjections tools first second of
    Nothing ->
        Monad.Trans.lift (Error.throwE (UnificationError UnsupportedPatterns))
    Just NotInjection -> empty
    Just NotMatching -> return (ExpandedPattern.bottom, SimplificationProof)
    Just
        (Matching SortInjectionMatch
            { injectionHead, sort, firstChild, secondChild }
        ) -> do
            (merged, _) <- Monad.Trans.lift $
                termMerger firstChild secondChild
            if ExpandedPattern.isBottom merged
                then return (ExpandedPattern.bottom, SimplificationProof)
                else return
                    ( applyInjection sort injectionHead <$> merged
                    , SimplificationProof
                    )
  where
    applyInjection sort injectionHead term = mkApp sort injectionHead [term]

data SortInjectionMatch level variable =
    SortInjectionMatch
        { injectionHead :: !(SymbolOrAlias level)
        , sort :: !(Sort level)
        , firstChild :: !(StepPattern level variable)
        , secondChild :: !(StepPattern level variable)
        }

data SortInjectionSimplification level variable
  = NotInjection
  | NotMatching
  | Matching !(SortInjectionMatch level variable)

simplifySortInjections
    ::  forall level variable .
        ( Ord (variable level)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> StepPattern level variable
    -> Maybe (SortInjectionSimplification level variable)
simplifySortInjections
    tools
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
          | firstOrigin `isSubsortOf` secondOrigin -> Just mergeFirstIntoSecond

          | secondOrigin `isSubsortOf` firstOrigin -> Just mergeSecondIntoFirst

          | isFirstConstructorLike || isSecondConstructorLike
            -> Just NotMatching

          | Set.null sortIntersection -> Just NotMatching

          | otherwise -> Nothing
  where
    subsorts = MetadataTools.subsorts tools

    firstHeadAttributes = MetadataTools.symAttributes tools firstHead
    secondHeadAttributes = MetadataTools.symAttributes tools secondHead

    StepperAttributes { sortInjection = SortInjection isFirstSortInjection } =
        firstHeadAttributes
    StepperAttributes { sortInjection = SortInjection isSecondSortInjection } =
        secondHeadAttributes

    isSubsortOf = MetadataTools.isSubsortOf tools

    isConstructorLike = isConstructorLikeTop tools . Recursive.project
    isFirstConstructorLike = isConstructorLike firstChild
    isSecondConstructorLike = isConstructorLike secondChild

    {- |
        Merge the terms inside a sort injection,

        \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
        ===
        \inj{src2, dst}(\inj{src1, src2}(a) ∧ b)

        when src1 is a subsort of src2.
     -}
    mergeFirstIntoSecond ::  SortInjectionSimplification level variable
    mergeFirstIntoSecond =
        Matching SortInjectionMatch
            { injectionHead = SymbolOrAlias
                { symbolOrAliasConstructor = firstConstructor
                , symbolOrAliasParams = [secondOrigin, firstDestination]
                }
            , sort = firstDestination
            , firstChild = sortInjection firstOrigin secondOrigin firstChild
            , secondChild = secondChild
            }

    {- |
        Merge the terms inside a sort injection,

        \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
        ===
        \inj{src1, dst}(a ∧ \inj{src2, src1}(b))

        when src2 is a subsort of src1.
     -}
    mergeSecondIntoFirst :: SortInjectionSimplification level variable
    mergeSecondIntoFirst =
        Matching SortInjectionMatch
            { injectionHead = SymbolOrAlias
                { symbolOrAliasConstructor = firstConstructor
                , symbolOrAliasParams = [firstOrigin, firstDestination]
                }
            , sort = firstDestination
            , firstChild = firstChild
            , secondChild = sortInjection secondOrigin firstOrigin secondChild
            }

    sortInjection
        :: Sort level
        -> Sort level
        -> StepPattern level variable
        -> StepPattern level variable
    sortInjection originSort destinationSort term =
        mkApp
            destinationSort
            SymbolOrAlias
                { symbolOrAliasConstructor = firstConstructor
                , symbolOrAliasParams = [originSort, destinationSort]
                }
            [term]
    firstSubsorts = subsorts firstOrigin
    secondSubsorts = subsorts secondOrigin
    sortIntersection = Set.intersection firstSubsorts secondSubsorts
simplifySortInjections _ _ _ = Just NotInjection

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
-- TODO (virgil): This implementation is provisional, we're not sure yet if sort
-- injection should always clash with constructors. We should clarify this.
constructorSortInjectionAndEquals
    ::  ( Eq (variable level)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
constructorSortInjectionAndEquals
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | isConstructorSortInjection =
    assert (firstHead /= secondHead) $
        return (mkBottom_, SimplificationProof)
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
    ::  ( Eq (variable level)
        , MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
constructorAndEqualsAssumesDifferentHeads
    tools
    (App_ firstHead _)
    (App_ secondHead _)
  | isConstructor firstHead && isConstructor secondHead =
    assert (firstHead /= secondHead) $
        return (mkBottom_, SimplificationProof)
  where
    isConstructor = give tools StepperAttributes.isConstructor_
constructorAndEqualsAssumesDifferentHeads _ _ _ = empty

{- | Unifcation or equality for a domain value pattern vs a constructor
application.

This unification case throws an error because domain values may not occur in a
sort with constructors.

-}
domainValueAndConstructorErrors
    :: ( Eq (variable level)
       , MetaOrObject level
       )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
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
    :: (Eq (variable Object), Eq level, Eq (variable level))
    => StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (Domain.BuiltinPattern _))
    second@(DV_ _ (Domain.BuiltinPattern _))
  =
    assert (first /= second) $ return (mkBottom_, SimplificationProof)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (Domain.BuiltinBool _))
    second@(DV_ _ (Domain.BuiltinBool _))
  =
    assert (first /= second) $ return (mkBottom_, SimplificationProof)
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ (Domain.BuiltinInteger _))
    second@(DV_ _ (Domain.BuiltinInteger _))
  =
    assert (first /= second) $ return (mkBottom_, SimplificationProof)
domainValueAndEqualsAssumesDifferent _ _ = empty

{-| Unify two literal strings.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
stringLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
stringLiteralAndEqualsAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  =
    assert (first /= second) $
        return (mkBottom_, SimplificationProof)
stringLiteralAndEqualsAssumesDifferent _ _ = empty

{-| Unify two literal characters.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
charLiteralAndEqualsAssumesDifferent
    :: Eq (variable Meta)
    => StepPattern level variable
    -> StepPattern level variable
    -> Maybe (StepPattern level variable, SimplificationProof level)
charLiteralAndEqualsAssumesDifferent
    first@(CharLiteral_ _)
    second@(CharLiteral_ _)
  =
    assert (first /= second) $
        return (mkBottom_, SimplificationProof)
charLiteralAndEqualsAssumesDifferent _ _ = empty

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate.

-}
functionAnd
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> StepPattern level variable
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
            , predicate = makeEqualsPredicate first second
            , substitution = mempty
            }
        , SimplificationProof
        )
  | otherwise = empty
