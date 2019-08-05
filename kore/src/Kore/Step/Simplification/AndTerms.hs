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
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT (..), fromMaybe, mapMaybeT )
import qualified Control.Error as Error
import           Control.Exception
                 ( assert )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC
import           Prelude hiding
                 ( concat )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike
import qualified Kore.Logger as Logger
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.PatternAttributes
                 ( isConstructorLikeTop )
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as SimplificationType
                 ( SimplificationType (..) )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather, scatter )
import           Kore.Step.Substitution
                 ( PredicateMerger,
                 createLiftedPredicatesAndSubstitutionsMerger,
                 createPredicatesAndSubstitutionsMergerExcept )
import           Kore.TopBottom
import           Kore.Unification.Error
                 ( unsupportedPatterns )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify as Unify
import           Kore.Unparser
import           Kore.Variables.Fresh

import {-# SOURCE #-} qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )

data SimplificationTarget = AndT | EqualsT | BothT

type TermSimplifier variable m =
    TermLike variable -> TermLike variable -> m (Pattern variable)

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

See also: 'termAnd'

 -}
termEquals
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (OrPredicate variable)
termEquals first second = MaybeT $ do
    tools <- Simplifier.askMetadataTools
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    simplifier <- Simplifier.askSimplifierTermLike
    axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
    maybeResults <-
        BranchT.gather $ runMaybeT $ termEqualsAnd
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            first
            second
    case sequence maybeResults of
        Nothing -> return Nothing
        Just results -> return $ Just $
            MultiOr.make (map Predicate.eraseConditionalTerm results)

termEqualsAnd
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> TermLike variable
    -> MaybeT (BranchT simplifier) (Pattern variable)
termEqualsAnd
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    p1
    p2
  = MaybeT
    $   either missingCase BranchT.scatter
        =<< (runUnifierT . runMaybeT) (maybeTermEqualsWorker p1 p2)
  where
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
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
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
                (alternate . BranchT.scatter)
            . sequence
        equalsPredicate =
            Conditional
                { term = mkTop_
                , predicate = makeEqualsPredicate first second
                , substitution = mempty
                }

maybeTermEquals
    ::  ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> PredicateMerger variable unifier
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
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
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
        tools <- Simplifier.askMetadataTools
        substitutionSimplifier <- Simplifier.askSimplifierPredicate
        simplifier <- Simplifier.askSimplifierTermLike
        axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
        let
            maybeTermUnification :: MaybeT unifier (Pattern variable)
            maybeTermUnification =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
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
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
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
        tools <- Simplifier.askMetadataTools
        substitutionSimplifier <- Simplifier.askSimplifierPredicate
        simplifier <- Simplifier.askSimplifierTermLike
        axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
        let maybeTermAnd' =
                maybeTermAnd
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    createLiftedPredicatesAndSubstitutionsMerger
                    termAndWorker
                    first
                    second
        patt <- runMaybeT maybeTermAnd'
        return $ fromMaybe andPattern patt
      where
        andPattern = Pattern.fromTermLike (mkAnd first second)

maybeTermAnd
    ::  ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermAnd = maybeTransformTerm andFunctions

andFunctions
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
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
    forAnd f = f SimplificationType.And

equalsFunctions
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
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
    forEquals f = f SimplificationType.Equals

andEqualsFunctions
    ::  forall variable unifier
    .   ( Eq variable
        , FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        , GHC.HasCallStack
        )
    => [(SimplificationTarget, TermTransformation variable unifier)]
andEqualsFunctions = fmap mapEqualsFunctions
    [ (AndT,    liftE0 boolAnd, "boolAnd")
    , (BothT,   liftET equalAndEquals, "equalAndEquals")
    , (EqualsT, lift0  bottomTermEquals, "bottomTermEquals")
    , (EqualsT, lift0  termBottomEquals, "termBottomEquals")
    , (BothT,   liftTS variableFunctionAndEquals, "variableFunctionAndEquals")
    , (BothT,   liftTS functionVariableAndEquals, "functionVariableAndEquals")
    , (BothT,   addT   equalInjectiveHeadsAndEquals, "equalInjectiveHeadsAndEquals")
    , (BothT,   addS   sortInjectionAndEqualsAssumesDifferentHeads, "sortInjectionAndEqualsAssumesDifferentHeads")
    , (BothT,   liftE1 constructorSortInjectionAndEquals, "constructorSortInjectionAndEquals")
    , (BothT,   liftE1 constructorAndEqualsAssumesDifferentHeads, "constructorAndEqualsAssumesDifferentHeads")
    , (BothT,   liftB1 Builtin.Map.unifyEquals, "Builtin.Map.unifyEquals")
    , (BothT,   liftB1 Builtin.Set.unifyEquals, "Builtin.Set.unifyEquals")
    , (BothT,   liftB  Builtin.List.unifyEquals, "Builtin.List.unifyEquals")
    , (BothT,   liftE  domainValueAndConstructorErrors, "domainValueAndConstructorErrors")
    , (BothT,   liftE0 domainValueAndEqualsAssumesDifferent, "domainValueAndEqualsAssumesDifferent")
    , (BothT,   liftE0 stringLiteralAndEqualsAssumesDifferent, "stringLiteralAndEqualsAssumesDifferent")
    , (BothT,   liftE0 charLiteralAndEqualsAssumesDifferent, "charLiteralAndEqualsAssumesDifferent")
    , (AndT,    lift   functionAnd, "functionAnd")
    ]
  where
    mapEqualsFunctions (target, termTransform, name) =
        (target, logTT name termTransform)

    logTT
        :: String
        -> TermTransformation variable unifier
        -> TermTransformation variable unifier
    logTT fnName termTransformation sType tools ps tls bs pm ts t1 t2 =
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
            $ termTransformation sType tools ps tls bs pm ts t1 t2

    liftB
        f
        simplificationType
        tools
        substitutionSimplifier
        _simplifier
        _axiomIdToSimplifier
        _substitutionMerger
      =
        f
            simplificationType
            tools
            substitutionSimplifier
    liftB1
        f
        simplificationType
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        _substitutionMerger
      =
        f
            simplificationType
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

    lift = pure . transformerLiftOld
    liftE = lift . toExpanded
    liftE0
        f
        _simplificationType
        _tools
        _substitutionSimplifier
        _simplifier
        _axiomIdToSimplifier
        _substitutionMerger
        _termSimplifier
        first
        second
      = Pattern.fromTermLike <$> f first second
    liftE1
        f
        _simplificationType
        tools
        _substitutionSimplifier
        _simplifier
        _axiomIdToSimplifier
        _substitutionMerger
        _termSimplifier
        first
        second
      = Pattern.fromTermLike <$> f tools first second
    liftET = liftE . addToolsArg
    addS
        f
        _simplificationType
        tools
        _substitutionSimplifier
        _simplifier
        _axiomIdToSimplifier
        _substitutionMerger
      = f tools
    addT
        ::  (  SmtMetadataTools Attribute.Symbol
            -> PredicateMerger variable unifier
            -> TermSimplifier variable unifier
            -> TermLike variable
            -> TermLike variable
            -> MaybeT unifier (Pattern variable)
            )
        -> TermTransformation variable unifier
    addT
        f
        _simplificationType
        tools
        _substitutionSimplifier
        _simplifier
        _axiomIdToSimplifier
      =
        f tools
    lift0
        f
        _simplificationType
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        _substitutionMerger
        _termSimplifier
        p1
        p2
      = f tools substitutionSimplifier simplifier axiomIdToSimplifier p1 p2
    liftTS
        f
        simplificationType
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        substitutionMerger
        _termSimplifier
      =
        f
            simplificationType
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            substitutionMerger


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
       SimplificationType
    -> SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

type TermTransformationOld variable unifier =
       SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> PredicateMerger variable unifier
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
    -> SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm pairs.
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTransformTerm
    topTransformers
    mergeException
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    childTransformers
    first
    second
  =
    Foldable.asum
        (map
            (\f -> f
                mergeException
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                childTransformers
                first
                second
            )
            topTransformers
        )

addToolsArg
    ::  (  TermLike variable
        -> TermLike variable
        -> Maybe (TermLike variable)
        )
    ->  (  SmtMetadataTools Attribute.Symbol
        -> TermLike variable
        -> TermLike variable
        -> Maybe (TermLike variable)
        )
addToolsArg = pure

toExpanded
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        )
    =>  (  SmtMetadataTools Attribute.Symbol
        -> TermLike variable
        -> TermLike variable
        -> Maybe (TermLike variable)
        )
    ->  (  SmtMetadataTools Attribute.Symbol
        -> TermLike variable
        -> TermLike variable
        -> Maybe (Pattern variable)
        )
toExpanded transformer tools first second =
    toExpanded0 <$> transformer tools first second
  where
    toExpanded0 term
      | isBottom term = Pattern.bottom
      | otherwise     = Pattern.fromTermLike term

transformerLiftOld
    :: Monad unifier
    =>  (  SmtMetadataTools Attribute.Symbol
        -> TermLike variable
        -> TermLike variable
        -> Maybe (Pattern variable)
        )
    -> TermTransformationOld variable unifier
transformerLiftOld
    transformation
    tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    _substitutionMerger
    _childSimplifier
    first
    second
  = liftPattern (transformation tools first second)

liftPattern
    :: Monad m
    => Maybe (Pattern variable)
    -> MaybeT m (Pattern variable)
liftPattern = MaybeT . return

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: MonadUnify unifier
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (TermLike variable)
boolAnd first second
  | isBottom first  = do
      explainBoolAndBottom first second
      return first
  | isTop first     = return second
  | isBottom second = do
      explainBoolAndBottom first second
      return second
  | isTop second    = return first
  | otherwise       = empty

explainBoolAndBottom
    :: MonadUnify unifier
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier ()
explainBoolAndBottom term1 term2 =
    Monad.Trans.lift $ explainBottom "Cannot unify bottom." term1 term2

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: Eq variable
    => TermLike variable
    -> TermLike variable
    -> Maybe (TermLike variable)
equalAndEquals first second
  | first == second =
    return first
equalAndEquals _ _ = empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
bottomTermEquals
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    first@(Bottom_ _)
    second
  = Monad.Trans.lift $ do -- MonadUnify
    secondCeil <- Ceil.makeEvaluateTerm second

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
bottomTermEquals _ _ _ _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termBottomEquals
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  =
    bottomTermEquals
        tools substitutionSimplifier simplifier axiomIdToSimplifier second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionAndEquals
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadUnify unifier
        , Logger.WithLog Logger.LogMessage unifier
        )
    => GHC.HasCallStack
    => SimplificationType
    -> SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> PredicateMerger variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAndEquals
    SimplificationType.And
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    _substitutionMerger
    first@(Var_ v1)
    second@(Var_ v2)
  =
    return Conditional
        { term = if v2 > v1 then second else first
        , predicate = makeTruePredicate
        , substitution =
            Substitution.wrap
                [ if v2 > v1 then (v1, second) else (v2, first) ]
        }
variableFunctionAndEquals
    simplificationType
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    _
    first@(Var_ v)
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
                resultOr <- Ceil.makeEvaluateTerm second
                case MultiOr.extractPatterns resultOr of
                    [] -> do
                        explainBottom
                           "Unification of variable and bottom \
                           \when attempting to simplify equals."
                           first
                           second
                        empty
                    resultPredicates -> Unify.scatter resultPredicates
    let result = predicate <> Predicate.fromSingleSubstitution (v, second)
    return (Pattern.withCondition second result)
variableFunctionAndEquals _ _ _ _ _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

 -}
functionVariableAndEquals
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => SimplificationType
    -> SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> PredicateMerger variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
functionVariableAndEquals
    simplificationType
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    substitutionMerger
    first
    second
  =
    variableFunctionAndEquals
        simplificationType
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        substitutionMerger
        second
        first

{- | Unify two application patterns with equal, injective heads.

This includes constructors and sort injections.

See also: 'Attribute.isInjective', 'Attribute.isSortInjection',
'Attribute.isConstructor'

 -}
equalInjectiveHeadsAndEquals
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> PredicateMerger variable unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
equalInjectiveHeadsAndEquals
    _tools
    _
    termMerger
    (App_ firstHead firstChildren)
    (App_ secondHead secondChildren)
  | isFirstInjective && isSecondInjective && firstHead == secondHead =
    Monad.Trans.lift $ do
        children <- Monad.zipWithM termMerger firstChildren secondChildren
        let merged = Foldable.foldMap Pattern.withoutTerm children
            term = mkApplySymbol firstHead (Pattern.term <$> children)
        return (Pattern.withCondition term merged)
  where
    isFirstInjective = Symbol.isInjective firstHead
    isSecondInjective = Symbol.isInjective secondHead

equalInjectiveHeadsAndEquals _ _ _ _ _ = Error.nothing

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
    => SmtMetadataTools Attribute.Symbol
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
sortInjectionAndEqualsAssumesDifferentHeads
    tools
    termMerger
    first
    second
  = case simplifySortInjections tools first second of
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
    Just
        (Matching SortInjectionMatch
            { injectionHead, firstChild, secondChild }
        ) -> Monad.Trans.lift $ do
            merged <- termMerger firstChild secondChild
            if Pattern.isBottom merged
                then do
                    explainBottom
                        "Unification of sort injections failed when \
                        \merging application children: the result is bottom."
                        first
                        second
                    empty
                else
                    return $ applyInjection injectionHead <$> merged
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
-- TODO (virgil): This implementation is provisional, we're not sure yet if sort
-- injection should always clash with constructors. We should clarify this.
constructorSortInjectionAndEquals
    ::  ( Eq variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (TermLike variable)
constructorSortInjectionAndEquals
    _tools
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
constructorSortInjectionAndEquals _ _ _ = empty

{-| Unify two constructor application patterns.

Assumes that the two patterns were already tested for equality and were found
to be different; therefore their conjunction is @\\bottom@.

 -}
constructorAndEqualsAssumesDifferentHeads
    ::  ( Eq variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (TermLike variable)
constructorAndEqualsAssumesDifferentHeads
    _tools
    first@(App_ firstHead _)
    second@(App_ secondHead _)
  | Symbol.isConstructor firstHead
  , Symbol.isConstructor secondHead =
    assert (firstHead /= secondHead) $ Monad.Trans.lift $ do
        explainBottom
            "Cannot unify different constructors or incompatible \
            \sort injections."
            first
            second
        empty
constructorAndEqualsAssumesDifferentHeads _ _ _ = empty

{- | Unifcation or equality for a domain value pattern vs a constructor
application.

This unification case throws an error because domain values may not occur in a
sort with constructors.

-}
domainValueAndConstructorErrors
    :: Eq variable
    => Unparse variable
    => SortedVariable variable
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> Maybe (TermLike variable)
domainValueAndConstructorErrors
    _tools
    term1@(DV_ _ _)
    term2@(App_ secondHead _)
    | Symbol.isConstructor secondHead =
      error (unlines [ "Cannot handle DomainValue and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    _tools
    term1@(Builtin_ _)
    term2@(App_ secondHead _)
    | Symbol.isConstructor secondHead =
      error (unlines [ "Cannot handle builtin and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    _tools
    term1@(App_ firstHead _)
    term2@(DV_ _ _)
    | Symbol.isConstructor firstHead =
      error (unlines [ "Cannot handle Constructor and DomainValue:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    _tools
    term1@(App_ firstHead _)
    term2@(Builtin_ _)
    | Symbol.isConstructor firstHead =
      error (unlines [ "Cannot handle Constructor and builtin:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors _ _ _ = empty

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
    -> MaybeT unifier (TermLike variable)
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
    -> unifier (TermLike variable)
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
    -> MaybeT unifier (TermLike variable)
stringLiteralAndEqualsAssumesDifferent
    first@(StringLiteral_ _)
    second@(StringLiteral_ _)
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
stringLiteralAndEqualsAssumesDifferent _ _ = empty

{-| Unify two literal characters.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
charLiteralAndEqualsAssumesDifferent
    :: Eq variable
    => SortedVariable variable
    => Unparse variable
    => MonadUnify unifier
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (TermLike variable)
charLiteralAndEqualsAssumesDifferent
    first@(CharLiteral_ _)
    second@(CharLiteral_ _)
  = Monad.Trans.lift $ cannotUnifyDomainValues first second
charLiteralAndEqualsAssumesDifferent _ _ = empty

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate.

-}
functionAnd
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => GHC.HasCallStack
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
    -> Maybe (Pattern variable)
functionAnd
    _tools
    first
    second
  | isFunctionPattern first, isFunctionPattern second =
    return Conditional
        { term = first  -- different for Equals
        -- Ceil predicate not needed since first being
        -- bottom will make the entire term bottom. However,
        -- one must be careful to not just drop the term.
        , predicate = makeEqualsPredicate first second
        , substitution = mempty
        }
  | otherwise = empty
