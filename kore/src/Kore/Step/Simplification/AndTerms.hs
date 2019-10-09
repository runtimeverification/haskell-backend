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
    , cannotUnifyDistinctDomainValues
    , functionAnd
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT (..)
    , fromMaybe
    , mapMaybeT
    )
import qualified Control.Error as Error
import Control.Exception
    ( assert
    )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import qualified Kore.Logger as Logger
import Kore.Predicate.Predicate
    ( pattern PredicateTrue
    , makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.PatternAttributes
    ( isConstructorLikeTop
    )
import Kore.Step.Simplification.ExpandAlias
    ( expandAlias
    )
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.Overloading
import Kore.Step.Simplification.SimplificationType
    ( SimplificationType
    )
import qualified Kore.Step.Simplification.SimplificationType as SimplificationType
    ( SimplificationType (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Substitution
    ( PredicateMerger
    , createLiftedPredicatesAndSubstitutionsMerger
    , createPredicatesAndSubstitutionsMergerExcept
    )
import Kore.TopBottom
import Kore.Unification.Error
    ( unsupportedPatterns
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify as Unify
import Kore.Unparser
import Kore.Variables.Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import {-# SOURCE #-} qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )

data SimplificationTarget = AndT | EqualsT | BothT

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

See also: 'termAnd'

 -}
termEquals
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (OrPredicate variable)
termEquals first second = MaybeT $ do
    maybeResults <- BranchT.gather $ runMaybeT $ termEqualsAnd first second
    case sequence maybeResults of
        Nothing -> return Nothing
        Just results -> return $ Just $
            MultiOr.make (map Predicate.eraseConditionalTerm results)

termEqualsAnd
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT (BranchT simplifier) (Pattern variable)
termEqualsAnd p1 p2 =
    MaybeT $ run $ maybeTermEqualsWorker p1 p2
  where
    run it = (runUnifierT . runMaybeT) it >>= either missingCase BranchT.scatter
    missingCase = const (return Nothing)

    maybeTermEqualsWorker
        :: forall unifier
        .   ( MonadUnify unifier
            , Logger.WithLog Logger.LogMessage unifier
            )
        => TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
    maybeTermEqualsWorker =
        maybeTermEquals
            createPredicatesAndSubstitutionsMergerExcept
            termEqualsAndWorker

    termEqualsAndWorker
        :: forall unifier
        .   ( MonadUnify unifier
            , Logger.WithLog Logger.LogMessage unifier
            )
        => TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termEqualsAndWorker first second =
        either ignoreErrors scatterResults
        =<< (runUnifierT . runMaybeT) (maybeTermEqualsWorker first second)
      where
        ignoreErrors _ = return equalsPredicate
        scatterResults =
            maybe
                (return equalsPredicate) -- default if no results
                (BranchT.alternate . BranchT.scatter)
            . sequence
        equalsPredicate =
            Conditional
                { term = mkTop_
                , predicate =
                    Syntax.Predicate.markSimplified
                    $ makeEqualsPredicate first second
                , substitution = mempty
                }

maybeTermEquals
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermEquals = maybeTransformTerm equalsFunctions

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

Unlike 'termAnd', @termUnification@ does not make an @\\and@ term when a
particular case is not implemented; otherwise, the two are the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

-}
-- NOTE (hs-boot): Please update the AndTerms.hs-boot file when changing the
-- signature.
termUnification
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
termUnification =
    termUnificationWorker
  where
    termUnificationWorker
        :: TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termUnificationWorker pat1 pat2 = do
        let
            maybeTermUnification :: MaybeT unifier (Pattern variable)
            maybeTermUnification =
                maybeTermAnd
                    createPredicatesAndSubstitutionsMergerExcept
                    termUnificationWorker
                    pat1
                    pat2
            unsupportedPatternsError =
                throwUnificationError
                    (unsupportedPatterns
                        "Unknown unification case."
                        pat1
                        pat2
                    )
        Error.maybeT unsupportedPatternsError pure maybeTermUnification

{- | Simplify the conjunction (@\\and@) of two terms.

The comment for 'Kore.Step.Simplification.And.simplify' describes all the
special cases
handled by this.

See also: 'termUnification'

-}
-- NOTE (hs-boot): Please update AndTerms.hs-boot file when changing the
-- signature.
termAnd
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> BranchT simplifier (Pattern variable)
termAnd p1 p2 =
    either (const andTerm) BranchT.scatter
    =<< (Monad.Trans.lift . runUnifierT) (termAndWorker p1 p2)
  where
    andTerm = return $ Pattern.fromTermLike (mkAnd p1 p2)
    termAndWorker
        ::  ( MonadUnify unifier
            , Logger.WithLog Logger.LogMessage unifier
            )
        => TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termAndWorker first second = do
        let maybeTermAnd' =
                maybeTermAnd
                    createLiftedPredicatesAndSubstitutionsMerger
                    termAndWorker
                    first
                    second
        patt <- runMaybeT maybeTermAnd'
        return $ fromMaybe andPattern patt
      where
        andPattern = Pattern.fromTermLike (mkAnd first second)

maybeTermAnd
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermAnd = maybeTransformTerm andFunctions

andFunctions
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        , GHC.HasCallStack
        )
    => [TermTransformationOld variable unifier]
andFunctions =
    map (forAnd . snd) (filter appliesToAnd andEqualsFunctions)
  where
    appliesToAnd :: (SimplificationTarget, a) -> Bool
    appliesToAnd (AndT, _) = True
    appliesToAnd (EqualsT, _) = False
    appliesToAnd (BothT, _) = True

    forAnd
        :: TermTransformation variable unifier
        -> TermTransformationOld variable unifier
    forAnd f = f Predicate.topTODO SimplificationType.And

equalsFunctions
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        , GHC.HasCallStack
        )
    => [TermTransformationOld variable unifier]
equalsFunctions =
    map (forEquals . snd) (filter appliesToEquals andEqualsFunctions)
  where
    appliesToEquals :: (SimplificationTarget, a) -> Bool
    appliesToEquals (AndT, _) = False
    appliesToEquals (EqualsT, _) = True
    appliesToEquals (BothT, _) = True

    forEquals
        :: TermTransformation variable unifier
        -> TermTransformationOld variable unifier
    forEquals f = f Predicate.topTODO SimplificationType.Equals

andEqualsFunctions
    ::  forall variable unifier
    .   ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        , GHC.HasCallStack
        )
    => [(SimplificationTarget, TermTransformation variable unifier)]
andEqualsFunctions = fmap mapEqualsFunctions
    [ (AndT,    \_ _ m s -> expandAlias (maybeTermAnd m s), "expandAlias")
    , (AndT,    \_ _ _ _ -> boolAnd, "boolAnd")
    , (BothT,   \_ _ _ _ -> equalAndEquals, "equalAndEquals")
    , (EqualsT, \p _ _ _ -> bottomTermEquals p, "bottomTermEquals")
    , (EqualsT, \p _ _ _ -> termBottomEquals p, "termBottomEquals")
    , (BothT,   \p t _ _ -> variableFunctionAndEquals p t, "variableFunctionAndEquals")
    , (BothT,   \p t _ _ -> functionVariableAndEquals p t, "functionVariableAndEquals")
    , (BothT,   \_ _ _ s -> equalInjectiveHeadsAndEquals s, "equalInjectiveHeadsAndEquals")
    , (BothT,   \_ _ _ s -> sortInjectionAndEqualsAssumesDifferentHeads s, "sortInjectionAndEqualsAssumesDifferentHeads")
    , (BothT,   \_ _ _ _ -> constructorSortInjectionAndEquals, "constructorSortInjectionAndEquals")
    , (BothT,   \_ _ _ _ -> constructorAndEqualsAssumesDifferentHeads, "constructorAndEqualsAssumesDifferentHeads")
    , (BothT,   \_ _ _ s -> overloadedConstructorSortInjectionAndEquals s, "overloadedConstructorSortInjectionAndEquals")
    , (BothT,   \_ _ _ s -> Builtin.Map.unifyEquals s, "Builtin.Map.unifyEquals")
    , (BothT,   \_ _ _ s -> Builtin.Set.unifyEquals s, "Builtin.Set.unifyEquals")
    , (BothT,   \_ t _ s -> Builtin.List.unifyEquals t s, "Builtin.List.unifyEquals")
    , (BothT,   \_ _ _ _ -> domainValueAndConstructorErrors, "domainValueAndConstructorErrors")
    , (BothT,   \_ _ _ _ -> domainValueAndEqualsAssumesDifferent, "domainValueAndEqualsAssumesDifferent")
    , (BothT,   \_ _ _ _ -> stringLiteralAndEqualsAssumesDifferent, "stringLiteralAndEqualsAssumesDifferent")
    , (AndT,    \_ _ _ _ t1 t2 -> Error.hoistMaybe $ functionAnd t1 t2, "functionAnd")
    ]
  where
    mapEqualsFunctions (target, termTransform, name) =
        (target, logTT name termTransform)

    logTT
        :: String
        -> TermTransformation variable unifier
        -> TermTransformation variable unifier
    logTT fnName termTransformation predicate sType pm ts t1 t2 =
        mapMaybeT (\getResult -> do
            mresult <- getResult
            case mresult of
                Nothing -> do
                    Logger.withLogScope (Logger.Scope "AndTerms")
                        . Logger.logDebug . Text.pack . show
                        $ Pretty.hsep
                            [ "Evaluator"
                            , Pretty.pretty fnName
                            , "does not apply."
                            ]
                    return mresult
                Just result -> do
                    Logger.withLogScope (Logger.Scope "AndTerms")
                        . Logger.logDebug . Text.pack . show
                        $ Pretty.vsep
                            [ Pretty.hsep
                                [ "Evaluator"
                                , Pretty.pretty fnName
                                ]
                            , Pretty.indent 4 $ Pretty.vsep
                                [ "First:"
                                , Pretty.indent 4 $ unparse t1
                                , "Second:"
                                , Pretty.indent 4 $ unparse t2
                                , "Result:"
                                , Pretty.indent 4 $ unparse result
                                ]
                            ]
                    return mresult
            )
            $ termTransformation predicate sType pm ts t1 t2

{- | Construct the conjunction or unification of two terms.

Each @TermTransformationOld@ should represent one unification case and each
unification case should be handled by only one @TermTransformationOld@. If the
pattern heads do not match the case under consideration, call 'empty' to allow
another case to handle the patterns. If the pattern heads do match the
unification case, then use 'Control.Monad.Trans.lift' to wrap the implementation
of that case.

All the @TermTransformationOld@s and similar functions defined in this module
call 'empty' unless given patterns matching their unification case.

 -}
type TermTransformation variable unifier =
       Predicate variable
    -> SimplificationType
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

type TermTransformationOld variable unifier =
       PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

maybeTransformTerm
    ::  ( FreshVariable variable
        , Ord variable
        , Ord variable
        , Ord variable
        , Show variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => [TermTransformationOld variable unifier]
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm pairs.
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTransformTerm
    topTransformers
    predicateMerger
    childTransformers
    first
    second
  = do
    Foldable.asum
        (map
            (\f -> f
                predicateMerger
                childTransformers
                first
                second
            )
            topTransformers
        )

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: MonadUnify unifier
    => SimplifierVariable variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
boolAnd first second
  | isBottom first  = do
      explainBoolAndBottom first second
      return (Pattern.fromTermLike first)
  | isTop first     = return (Pattern.fromTermLike second)
  | isBottom second = do
      explainBoolAndBottom first second
      return (Pattern.fromTermLike second)
  | isTop second    = return (Pattern.fromTermLike first)
  | otherwise       = empty

explainBoolAndBottom
    :: MonadUnify unifier
    => SimplifierVariable variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier ()
explainBoolAndBottom term1 term2 =
    Monad.Trans.lift $ explainBottom "Cannot unify bottom." term1 term2

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: SimplifierVariable variable
    => Monad unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
equalAndEquals first second
  | first == second =
    return (Pattern.fromTermLike first)
equalAndEquals _ _ = empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => Predicate variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
bottomTermEquals
    predicate
    first@(Bottom_ _)
    second
  = Monad.Trans.lift $ do -- MonadUnify
    secondCeil <- Ceil.makeEvaluateTerm predicate second

    case MultiOr.extractPatterns secondCeil of
        [] -> return Pattern.top
        [ Conditional { predicate = PredicateTrue, substitution } ]
          | substitution == mempty -> do
            explainBottom
                "Cannot unify bottom with non-bottom pattern."
                first
                second
            empty
        _ ->
            return  Conditional
                { term = mkTop_
                , predicate =
                    makeNotPredicate
                    $ OrPredicate.toPredicate
                    $ Predicate.toPredicate <$> secondCeil
                , substitution = mempty
                }
bottomTermEquals _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => Predicate variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termBottomEquals predicate first second =
    bottomTermEquals predicate second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionAndEquals
    ::  ( SimplifierVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => Predicate variable
    -> SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAndEquals
    _
    SimplificationType.And
    first@(ElemVar_ v1)
    second@(ElemVar_ v2)
  =
    return Conditional
        { term = if v2 > v1 then second else first
        , predicate = makeTruePredicate
        , substitution =
            Substitution.wrap
                [ if v2 > v1 then (ElemVar v1, second) else (ElemVar v2, first)
                ]
        }
variableFunctionAndEquals
    configurationPredicate
    simplificationType
    first@(ElemVar_ v)
    second
  | isFunctionPattern second = Monad.Trans.lift $ do -- MonadUnify
    predicate <-
        case simplificationType of -- Simplifier
            SimplificationType.And ->
                -- Ceil predicate not needed since 'second' being bottom
                -- will make the entire term bottom. However, one must
                -- be careful to not just drop the term.
                return Predicate.top
            SimplificationType.Equals -> do
                resultOr <- Ceil.makeEvaluateTerm configurationPredicate second
                case MultiOr.extractPatterns resultOr of
                    [] -> do
                        explainBottom
                           "Unification of variable and bottom \
                           \when attempting to simplify equals."
                           first
                           second
                        empty
                    resultPredicates -> Unify.scatter resultPredicates
    let result =
            predicate <> Predicate.fromSingleSubstitution (ElemVar v, second)
    return (Pattern.withCondition second result)
variableFunctionAndEquals _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

 -}
functionVariableAndEquals
    :: (SimplifierVariable variable, MonadUnify unifier)
    => GHC.HasCallStack
    => Predicate variable
    -> SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
functionVariableAndEquals predicate simplificationType first second =
    variableFunctionAndEquals predicate simplificationType second first

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
    ::  forall variable unifier
    .   ( Ord variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
sortInjectionAndEqualsAssumesDifferentHeads termMerger first second = do
    tools <- Simplifier.askMetadataTools
    case simplifySortInjections tools first second of
        Nothing ->
            Monad.Trans.lift
                $ throwUnificationError
                $ unsupportedPatterns
                    "Unimplemented sort injection unification"
                    first
                    second
        Just NotInjection -> empty
        Just NotMatching -> Monad.Trans.lift $ do
            explainBottom
                "Unification of sort injections failed due to mismatch. \
                \This can happen either because one of them is a constructor \
                \or because their sort intersection is empty."
                first
                second
            empty
        Just (Matching sortInjectionMatch) -> Monad.Trans.lift $ do
            merged <- termMerger firstChild secondChild
            if Pattern.isBottom merged
                then do
                    explainBottom
                        "Unification of sort injections failed when \
                        \merging application children: \
                        \the result is bottom."
                        first
                        second
                    empty
                else
                    return $ applyInjection injectionHead <$> merged
          where
            SortInjectionMatch { firstChild, secondChild } = sortInjectionMatch
            SortInjectionMatch { injectionHead } = sortInjectionMatch
  where
    applyInjection injectionHead term = mkApplySymbol injectionHead [term]

data SortInjectionMatch variable =
    SortInjectionMatch
        { injectionHead :: !Symbol
        , sort :: !Sort
        , firstChild :: !(TermLike variable)
        , secondChild :: !(TermLike variable)
        }

data SortInjectionSimplification variable
  = NotInjection
  | NotMatching
  | Matching !(SortInjectionMatch variable)

simplifySortInjections
    :: forall variable
    .  (Ord variable, SortedVariable variable, Unparse variable)
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> Maybe (SortInjectionSimplification variable)
simplifySortInjections
    tools
    (App_
        firstHead@Symbol
            { symbolConstructor = firstConstructor
            , symbolParams = [firstOrigin, firstDestination]
            }
        [firstChild])
    (App_
        secondHead@Symbol
            { symbolConstructor = secondConstructor
            , symbolParams = [secondOrigin, secondDestination]
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

    isFirstSortInjection = Symbol.isSortInjection firstHead
    isSecondSortInjection = Symbol.isSortInjection firstHead

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
    mergeFirstIntoSecond ::  SortInjectionSimplification variable
    mergeFirstIntoSecond =
        Matching SortInjectionMatch
            { injectionHead = secondHead
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
    mergeSecondIntoFirst :: SortInjectionSimplification variable
    mergeSecondIntoFirst =
        Matching SortInjectionMatch
            { injectionHead = firstHead
            , sort = firstDestination
            , firstChild = firstChild
            , secondChild = sortInjection secondOrigin firstOrigin secondChild
            }

    sortInjection
        :: Sort
        -> Sort
        -> TermLike variable
        -> TermLike variable
    sortInjection originSort destinationSort term =
        mkApplySymbol
            (Symbol.coerceSortInjection firstHead originSort destinationSort)
            [term]
    firstSubsorts = subsorts firstOrigin
    secondSubsorts = subsorts secondOrigin
    sortIntersection = Set.intersection firstSubsorts secondSubsorts
simplifySortInjections _ _ _ = Just NotInjection

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
constructorSortInjectionAndEquals
    ::  ( Eq variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
constructorSortInjectionAndEquals
    first@(App_ firstHead _)
    second@(App_ secondHead _)
  | isConstructorSortInjection =
    assert (firstHead /= secondHead) $ Monad.Trans.lift $ do
        explainBottom
            "Cannot unify constructors with sort injections."
            first
            second
        empty
  where
    -- Are we asked to unify a constructor with a sort injection?
    isConstructorSortInjection =
        (||)
            (Symbol.isConstructor   firstHead && Symbol.isSortInjection secondHead)
            (Symbol.isSortInjection firstHead && Symbol.isConstructor   secondHead)
constructorSortInjectionAndEquals _ _ = empty

{- | Unifcation or equality for a domain value pattern vs a constructor
application.

This unification case throws an error because domain values may not occur in a
sort with constructors.

-}
domainValueAndConstructorErrors
    :: (Eq variable, Unparse variable, SortedVariable variable)
    => Monad unifier
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
domainValueAndConstructorErrors
    term1@(DV_ _ _)
    term2@(App_ secondHead _)
    | Symbol.isConstructor secondHead =
      error (unlines [ "Cannot handle DomainValue and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    term1@(Builtin_ _)
    term2@(App_ secondHead _)
    | Symbol.isConstructor secondHead =
      error (unlines [ "Cannot handle builtin and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    term1@(App_ firstHead _)
    term2@(DV_ _ _)
    | Symbol.isConstructor firstHead =
      error (unlines [ "Cannot handle Constructor and DomainValue:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    term1@(App_ firstHead _)
    term2@(Builtin_ _)
    | Symbol.isConstructor firstHead =
      error (unlines [ "Cannot handle Constructor and builtin:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors _ _ = empty

{- | Unify two domain values.

The two patterns are assumed to be inequal; therefore this case always return
@\\bottom@.

See also: 'equalAndEquals'

-}
-- TODO (thomas.tuegel): This unification case assumes that \dv is injective,
-- but it is not.
domainValueAndEqualsAssumesDifferent
    :: Eq variable
    => SortedVariable variable
    => Unparse variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
domainValueAndEqualsAssumesDifferent
    first@(DV_ _ _)
    second@(DV_ _ _)
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
domainValueAndEqualsAssumesDifferent
    first@(Builtin_ (Domain.BuiltinBool _))
    second@(Builtin_ (Domain.BuiltinBool _))
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
domainValueAndEqualsAssumesDifferent
    first@(Builtin_ (Domain.BuiltinInt _))
    second@(Builtin_ (Domain.BuiltinInt _))
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
domainValueAndEqualsAssumesDifferent
    first@(Builtin_ (Domain.BuiltinString _))
    second@(Builtin_ (Domain.BuiltinString _))
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
domainValueAndEqualsAssumesDifferent _ _ = empty

cannotUnifyDistinctDomainValues :: Pretty.Doc ()
cannotUnifyDistinctDomainValues = "Cannot unify distinct domain values."

cannotUnifyDomainValues
    :: Eq variable
    => SortedVariable variable
    => Unparse variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> unifier a
cannotUnifyDomainValues first second =
    assert (first /= second) $ do
        explainBottom
            cannotUnifyDistinctDomainValues
            first
            second
        empty

{-| Unify two literal strings.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
stringLiteralAndEqualsAssumesDifferent
    :: Eq variable
    => SortedVariable variable
    => Unparse variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
stringLiteralAndEqualsAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
stringLiteralAndEqualsAssumesDifferent _ _ = empty

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate.

-}
functionAnd
    :: SimplifierVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> Maybe (Pattern variable)
functionAnd first second
  | isFunctionPattern first, isFunctionPattern second =
    return Conditional
        { term = first  -- different for Equals
        -- Ceil predicate not needed since first being
        -- bottom will make the entire term bottom. However,
        -- one must be careful to not just drop the term.
        , predicate =
            Syntax.Predicate.markSimplified
            $ makeEqualsPredicate first second
        , substitution = mempty
        }
  | otherwise = empty
