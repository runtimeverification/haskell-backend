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
    , termUnification
    , maybeTermAnd
    , maybeTermEquals
    , SortInjectionMatch (..)
    , SortInjectionSimplification (..)
    , TermSimplifier
    , TermTransformationOld
    , cannotUnifyDistinctDomainValues
    , functionAnd
    , equalsFunctions
    , andFunctions
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT (..)
    , mapMaybeT
    )
import qualified Control.Error as Error
import Control.Exception
    ( assert
    )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concat
    )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Endianness as Builtin.Endianness
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Builtin.Signedness as Builtin.Signedness
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( pattern PredicateTrue
    , makeEqualsPredicate_
    , makeNotPredicate
    , makeTruePredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import qualified Kore.Logger as Logger
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
import Kore.TopBottom
import Kore.Unification.Error
    ( unsupportedPatterns
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify as Unify
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import {-# SOURCE #-} qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluateTerm
    )

data SimplificationTarget = AndT | EqualsT | BothT

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

Unlike 'termAnd', @termUnification@ does not make an @\\and@ term when a
particular case is not implemented; otherwise, the two are the same.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

-}
termUnification
    :: forall variable unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
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
            maybeTermUnification = maybeTermAnd termUnificationWorker pat1 pat2
            unsupportedPatternsError =
                throwUnificationError
                    (unsupportedPatterns
                        "Unknown unification case."
                        pat1
                        pat2
                    )
        Error.maybeT unsupportedPatternsError pure maybeTermUnification

maybeTermEquals
    :: SimplifierVariable variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermEquals = maybeTransformTerm equalsFunctions

maybeTermAnd
    :: SimplifierVariable variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermAnd = maybeTransformTerm andFunctions

andFunctions
    :: forall variable unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
    => GHC.HasCallStack
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
    forAnd f = f Condition.topTODO SimplificationType.And

equalsFunctions
    :: forall variable unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
    => GHC.HasCallStack
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
    forEquals f = f Condition.topTODO SimplificationType.Equals

andEqualsFunctions
    :: forall variable unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => [(SimplificationTarget, TermTransformation variable unifier)]
andEqualsFunctions = fmap mapEqualsFunctions
    [ (AndT,    \_ _ s -> expandAlias (maybeTermAnd s), "expandAlias")
    , (AndT,    \_ _ _ -> boolAnd, "boolAnd")
    , (BothT,   \_ _ _ -> equalAndEquals, "equalAndEquals")
    , (EqualsT, \p _ _ -> bottomTermEquals p, "bottomTermEquals")
    , (EqualsT, \p _ _ -> termBottomEquals p, "termBottomEquals")
    , (BothT,   \p t _ -> variableFunctionAndEquals p t, "variableFunctionAndEquals")
    , (BothT,   \p t _ -> functionVariableAndEquals p t, "functionVariableAndEquals")
    , (BothT,   \_ _ s -> equalInjectiveHeadsAndEquals s, "equalInjectiveHeadsAndEquals")
    , (BothT,   \_ _ s -> sortInjectionAndEqualsAssumesDifferentHeads s, "sortInjectionAndEqualsAssumesDifferentHeads")
    , (BothT,   \_ _ _ -> constructorSortInjectionAndEquals, "constructorSortInjectionAndEquals")
    , (BothT,   \_ _ _ -> constructorAndEqualsAssumesDifferentHeads, "constructorAndEqualsAssumesDifferentHeads")
    , (BothT,   \_ _ s -> overloadedConstructorSortInjectionAndEquals s, "overloadedConstructorSortInjectionAndEquals")
    , (BothT,   \_ _ _ -> Builtin.Endianness.unifyEquals, "Builtin.Endianness.unifyEquals")
    , (BothT,   \_ _ _ -> Builtin.Signedness.unifyEquals, "Builtin.Signedness.unifyEquals")
    , (BothT,   \_ _ s -> Builtin.Map.unifyEquals s, "Builtin.Map.unifyEquals")
    , (BothT,   \_ _ s -> Builtin.Set.unifyEquals s, "Builtin.Set.unifyEquals")
    , (BothT,   \_ t s -> Builtin.List.unifyEquals t s, "Builtin.List.unifyEquals")
    , (BothT,   \_ _ _ -> domainValueAndConstructorErrors, "domainValueAndConstructorErrors")
    , (BothT,   \_ _ _ -> domainValueAndEqualsAssumesDifferent, "domainValueAndEqualsAssumesDifferent")
    , (BothT,   \_ _ _ -> stringLiteralAndEqualsAssumesDifferent, "stringLiteralAndEqualsAssumesDifferent")
    , (AndT,    \_ _ _ t1 t2 -> Error.hoistMaybe $ functionAnd t1 t2, "functionAnd")
    ]
  where
    mapEqualsFunctions (target, termTransform, name) =
        (target, logTT name termTransform)

    logTT
        :: String
        -> TermTransformation variable unifier
        -> TermTransformation variable unifier
    logTT fnName termTransformation predicate sType ts t1 t2 =
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
            $ termTransformation predicate sType ts t1 t2

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
       Condition variable
    -> SimplificationType
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

type TermTransformationOld variable unifier =
       TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

maybeTransformTerm
    :: MonadUnify unifier
    => [TermTransformationOld variable unifier]
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm pairs.
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTransformTerm topTransformers childTransformers first second =
    Foldable.asum
        (map
            (\f -> f
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
    :: SimplifierVariable variable
    => MonadUnify unifier
    => Condition variable
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
                    $ OrCondition.toPredicate
                    $ Condition.toPredicate <$> secondCeil
                , substitution = mempty
                }
bottomTermEquals _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    :: SimplifierVariable variable
    => MonadUnify unifier
    => Condition variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termBottomEquals predicate first second =
    bottomTermEquals predicate second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionAndEquals
    :: SimplifierVariable variable
    => MonadUnify unifier
    => Condition variable
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
        , predicate = makeTruePredicate_
        , substitution =
            Substitution.wrap
                [ if v2 > v1 then (ElemVar v1, second) else (ElemVar v2, first)
                ]
        }
variableFunctionAndEquals
    configurationCondition
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
                return Condition.top
            SimplificationType.Equals -> do
                resultOr <- Ceil.makeEvaluateTerm configurationCondition second
                case MultiOr.extractPatterns resultOr of
                    [] -> do
                        explainBottom
                           "Unification of variable and bottom \
                           \when attempting to simplify equals."
                           first
                           second
                        empty
                    resultConditions -> Unify.scatter resultConditions
    let result =
            predicate <> Condition.fromSingleSubstitution (ElemVar v, second)
    return (Pattern.withCondition second result)
variableFunctionAndEquals _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

 -}
functionVariableAndEquals
    :: (SimplifierVariable variable, MonadUnify unifier)
    => Condition variable
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
    .   ( InternalVariable variable
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
    .  InternalVariable variable
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

    isFirstConstructorLike = hasConstructorLikeTop firstChild
    isSecondConstructorLike = hasConstructorLikeTop secondChild

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
    ::  ( SimplifierVariable variable
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
    :: SimplifierVariable variable
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
            Predicate.markSimplified
            $ makeEqualsPredicate_ first second
        , substitution = mempty
        }
  | otherwise = empty
