{-|
Module      : Kore.Step.Axiom.Matcher
Description : Matches free-form patterns which can be used when applying
              Equals rules.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.Matcher
    ( matchAsUnification
    , unificationWithAppMatchOnTop
    ) where

import           Control.Applicative
                 ( (<|>) )
import           Control.Error.Util
                 ( just, nothing )
import qualified Control.Monad as Monad
import           Control.Monad.Except
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Maybe
                 ( MaybeT (..) )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( on )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import           Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Domain.Builtin as Builtin
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.Simplification.AndTerms
                 ( SortInjectionMatch (SortInjectionMatch),
                 simplifySortInjections )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionMatch
                 ( SortInjectionMatch (..) )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionSimplification
                 ( SortInjectionSimplification (..) )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import qualified Kore.Step.Simplification.Data as Simplifier
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMergerExcept,
                 mergePredicatesAndSubstitutionsExcept )
import           Kore.Unification.Error
                 ( unsupportedPatterns )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- Matches two patterns based on their form.

Assumes that the two patterns have no common variables (quantified or not).

Returns Right bottom or Left when it can't handle the patterns. The
returned substitution substitutes only variables from the first pattern.

The meaning of a Right value is that the substitution holds IF the predicate
holds.

TODO: This is different from unification's meaning, so we should either
convert all bottoms to Left, or we should do it selectively. Doing
it selectively is not trivial, e.g. a bottom inside a function should become
Left, but inside a constructor we may be able to keep it as bottom.
-}
matchAsUnification
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
matchAsUnification first second = do
    result <- runMaybeT $ match Map.empty first second
    maybe
        (Monad.Unify.throwUnificationError
            (unsupportedPatterns "Unknown match case." first second)
        )
        return
        result

unificationWithAppMatchOnTop
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
unificationWithAppMatchOnTop first second =
    case first of
        (App_ firstHead firstChildren) ->
            case second of
                (App_ secondHead secondChildren)
                  | firstHead == secondHead
                    -> unifyJoin (zip firstChildren secondChildren)
                  | symbolConstructor firstHead == symbolConstructor secondHead
                    -- The application heads have the same symbol or alias
                    -- constructor with different parameters,
                    -- but we do not handle unification of symbol parameters.
                        -> Monad.Unify.throwUnificationError
                            (unsupportedPatterns
                                "Unknown application head match case for "
                                first
                                second
                            )
                  | otherwise
                    -> error
                        (  "Unexpected unequal heads: "
                        ++ show firstHead ++ " and "
                        ++ show secondHead ++ "."
                        )
                _ -> error
                    (  "Expecting application patterns, but second = "
                    ++ show second ++ "."
                    )
        (Ceil_ firstOperandSort (SortVariableSort _) firstChild) ->
            case second of
                (Ceil_ secondOperandSort _resultSort secondChild)
                  | firstOperandSort == secondOperandSort ->
                    unificationWithAppMatchOnTop firstChild secondChild
                  | otherwise
                        -> error
                            (  "Unexpected unequal child sorts: "
                            ++ show firstOperandSort ++ " and "
                            ++ show secondOperandSort ++ "."
                            )
                _ -> error
                    (  "Expecting ceil patterns, but second = "
                    ++ show second ++ "."
                    )
        _ -> error
            (  "Expecting application or ceil with sort variable patterns, "
            ++ "but first = " ++ show first ++ "."
            )

match
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => Map.Map variable variable
    -- ^ Quantified variables
    -> TermLike variable
    -> TermLike variable
    -- TODO: Use Result here.
    -> MaybeT unifier (Predicate variable)
match quantifiedVariables first second =
    (<|>)
        (matchEqualHeadPatterns quantifiedVariables first second)
        (matchVariableFunction quantifiedVariables first second)

matchEqualHeadPatterns
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => Map.Map variable variable
    -- ^ Quantified variables
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Predicate variable)
matchEqualHeadPatterns quantifiedVariables first second = do
    tools <- Simplifier.askMetadataTools
    case first of
        (And_ _ firstFirst firstSecond) ->
            case second of
                (And_ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (App_ firstHead firstChildren) ->
            case second of
                (App_ secondHead secondChildren) ->
                    if firstHead == secondHead
                    then
                        matchJoin
                            quantifiedVariables
                            (zip firstChildren secondChildren)
                    else case simplifySortInjections tools first second of
                        Nothing -> nothing
                        Just SortInjectionSimplification.NotInjection ->
                            nothing
                        Just SortInjectionSimplification.NotMatching ->
                            nothing
                        Just
                            (SortInjectionSimplification.Matching
                                SortInjectionMatch
                                    { firstChild, secondChild }
                            ) ->
                                matchJoin
                                    quantifiedVariables
                                    [(firstChild, secondChild)]
                (Builtin_ b2) ->
                    matchAppBuiltins
                        quantifiedVariables
                        firstHead
                        firstChildren
                        b2
                _ -> nothing
        (Bottom_ _) -> topWhenEqualOrNothing first second
        (Ceil_ _ _ firstChild) ->
            case second of
                (Ceil_ _ _ secondChild) ->
                    match quantifiedVariables firstChild secondChild
                _ -> nothing
        (CharLiteral_ _) ->
            topWhenEqualOrNothing first second
        (Builtin_ b1) ->
            (<|>)
                (topWhenEqualOrNothing first second)
                $ case second of
                    (Builtin_ b2) -> matchBuiltins quantifiedVariables b1 b2
                    _             -> nothing
        (DV_ _ _) ->
            topWhenEqualOrNothing first second
        (Equals_ _ _ firstFirst firstSecond) ->
            case second of
                (Equals_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Exists_ _ firstVariable firstChild) ->
            case second of
                (Exists_ _ secondVariable secondChild) ->
                    checkVariableEscape [firstVariable, secondVariable]
                    <$> match
                        (Map.insert
                            firstVariable secondVariable quantifiedVariables
                        )
                        firstChild
                        secondChild
                _ -> nothing
        (Floor_ _ _ firstChild) ->
            case second of
                (Floor_ _ _ secondChild) ->
                    match
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (Forall_ _ firstVariable firstChild) ->
            case second of
                (Forall_ _ secondVariable secondChild) ->
                    (<$>)
                        (checkVariableEscape [firstVariable, secondVariable])
                        (match
                            (Map.insert
                                firstVariable
                                secondVariable
                                quantifiedVariables
                            )
                            firstChild
                            secondChild
                        )
                _ -> nothing
        (Iff_ _ firstFirst firstSecond) ->
            case second of
                (Iff_ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Implies_ _ firstFirst firstSecond) ->
            case second of
                (Implies_ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (In_ _ _ firstFirst firstSecond) ->
            case second of
                (In_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Next_ _ firstChild) ->
            case second of
                (Next_ _ secondChild) ->
                    match quantifiedVariables firstChild secondChild
                _ -> nothing
        (Not_ _ firstChild) ->
            case second of
                (Not_ _ secondChild) ->
                    match quantifiedVariables firstChild secondChild
                _ -> nothing
        (Or_ _ firstFirst firstSecond) ->
            case second of
                (Or_ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Rewrites_ _ firstFirst firstSecond) ->
            case second of
                (Rewrites_ _ secondFirst secondSecond) ->
                    matchJoin
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (StringLiteral_ _) -> topWhenEqualOrNothing first second
        (Top_ _) -> topWhenEqualOrNothing first second
        (Var_ firstVariable) ->
            case second of
                (Var_ secondVariable) ->
                    case Map.lookup firstVariable quantifiedVariables of
                        Nothing -> nothing
                        Just variable ->
                            if variable == secondVariable
                            then justTop
                            else nothing
                _ -> nothing
        _ -> nothing
  where
    topWhenEqualOrNothing first' second' =
        if first' == second'
            then justTop
            else nothing
    justTop :: MaybeT unifier (Predicate variable)
    justTop = just Predicate.top

matchJoin
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => Map.Map variable variable
    -- ^ Quantified variables
    -> [(TermLike variable, TermLike variable)]
    -> MaybeT unifier (Predicate variable)
matchJoin quantifiedVariables patterns = do
    matched <-
        traverse  -- also does a cross-product of the unifier branches
            (uncurry $ match quantifiedVariables)
            patterns
    lift $ mergePredicatesAndSubstitutionsExcept
        (map Conditional.predicate matched)
        (map Conditional.substitution matched)

unifyJoin
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => [(TermLike variable, TermLike variable)]
    -> unifier (Predicate variable)
unifyJoin patterns = do
    predicates <- traverse (uncurry unificationProcedure) patterns
    return (Foldable.fold predicates)

-- Note that we can't match variables to stuff which can have more than one
-- value, because if we take the axiom
-- x = x and exists y . y=x
-- and we try to apply it to, say, 'a or b', where a and b are constructors
-- without arguments, then we would get
-- a or b
--   = (a or b) and (exists y . y = (a or b))
--   = (a or b) and bottom
--   = bottom
--
-- However, we can match variables to non-total stuff by using ceil to
-- force the match to bottom whenever we lose totality. This
-- assumes that, when applying the match to a pattern p, it will be split
-- into (p-replacing-lhs-by-rhs[subst] and predicate) or (p and not predicate)
matchVariableFunction
    ::  ( FreshVariable variable
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => Map.Map variable variable
    -- ^ Quantified variables
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Predicate variable)
matchVariableFunction quantifiedVariables (Var_ var) second
  | not (var `Map.member` quantifiedVariables) = do
    Monad.guard (isFunctionPattern second)
    Monad.Trans.lift $ do
        ceilOr <- Ceil.makeEvaluateTerm second
        result <-
            OrPattern.mergeWithPredicateAssumesEvaluated
                createPredicatesAndSubstitutionsMergerExcept
                (Conditional.fromSingleSubstitution (var, second))
                ceilOr
        Monad.Unify.scatter result
matchVariableFunction _ _ _ = nothing

checkVariableEscape
    ::  ( Show variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => [variable]
    -> Predicate variable
    -> Predicate variable
checkVariableEscape vars predSubst
  | any (`isFreeVariable` freeVars) vars = error
        "quantified variables in substitution or predicate escaping context"
  | otherwise = predSubst
  where
    freeVars = Predicate.freeVariables predSubst

matchAppBuiltins
    :: forall variable unifier
    .  FreshVariable variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => MonadUnify unifier
    => Map.Map variable variable
    -> Symbol
    -> [TermLike variable]
    -> Builtin.Builtin (TermLike Concrete) (TermLike variable)
    -> MaybeT unifier (Predicate variable)
matchAppBuiltins qv symbol args (Builtin.BuiltinList l2)
  | symbol == Builtin.builtinListConcat l2 =
    case args of
        [ Builtin_ (Builtin.BuiltinList l1), x@(Var_ _) ] -> do
            let (prefix2, suffix2) = splitByL2 (listLength l1) l2
            prefix  <-
                matchBuiltins
                    qv
                    (Builtin.BuiltinList l1)
                    (Builtin.BuiltinList prefix2)
            suffix <- match qv x (mkBuiltin $ Builtin.BuiltinList suffix2)
            pure $ prefix <> suffix
        [ x@(Var_ _), Builtin_ (Builtin.BuiltinList l1) ] -> do
            let (prefix2, suffix2) = splitByL2 (listLength l2 - listLength l1) l2
            prefix <- match qv x (mkBuiltin $ Builtin.BuiltinList prefix2)
            suffix  <-
                matchBuiltins
                    qv
                    (Builtin.BuiltinList l1)
                    (Builtin.BuiltinList suffix2)
            pure $ prefix <> suffix
        _ -> nothing
  where
    listLength :: Builtin.InternalList (TermLike variable) -> Int
    listLength = Seq.length . Builtin.builtinListChild

    splitByL2
        :: Int
        -> Builtin.InternalList (TermLike variable)
        ->  ( Builtin.InternalList (TermLike variable)
            , Builtin.InternalList (TermLike variable)
            )
    splitByL2 idx l =
        Bifunctor.bimap
            (updateInnerList l)
            (updateInnerList l)
            $ Seq.splitAt idx (Builtin.builtinListChild l)

    updateInnerList l newValue = l { Builtin.builtinListChild = newValue }
matchAppBuiltins _ _ _ _ = nothing

matchBuiltins
    :: FreshVariable variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => MonadUnify unifier
    => Map.Map variable variable
    -> Builtin.Builtin (TermLike Concrete) (TermLike variable)
    -> Builtin.Builtin (TermLike Concrete) (TermLike variable)
    -> MaybeT unifier (Predicate variable)
matchBuiltins qv (Builtin.BuiltinList l1) (Builtin.BuiltinList l2)
  | ((==) `on` Seq.length) seq1 seq2 =
    fmap Foldable.fold
        . traverse match'
        $ Seq.zip seq1 seq2
  where
    seq1 = Builtin.builtinListChild l1
    seq2 = Builtin.builtinListChild l2
    match' = uncurry (match qv)
matchBuiltins qv (Builtin.BuiltinSet s1) (Builtin.BuiltinSet s2) =
    matchAc
        qv
        builtinAcSort
        (Builtin.unwrapAc wrapped1)
        (Builtin.unwrapAc wrapped2)
  where
    Builtin.InternalAc { builtinAcChild = wrapped1 } = s1
    Builtin.InternalAc { builtinAcChild = wrapped2, builtinAcSort } = s2
matchBuiltins qv (Builtin.BuiltinMap m1) (Builtin.BuiltinMap m2) =
    matchAc
        qv
        builtinAcSort
        (Builtin.unwrapAc wrapped1)
        (Builtin.unwrapAc wrapped2)
  where
    Builtin.InternalAc { builtinAcChild = wrapped1 } = m1
    Builtin.InternalAc { builtinAcChild = wrapped2, builtinAcSort } = m2
matchBuiltins _ _ _ = nothing

matchAc
    :: forall normalized unifier valueWrapper variable
    .   ( Builtin.AcWrapper normalized
        , Foldable valueWrapper
        , FreshVariable variable
        , Simplifier.MonadSimplify unifier
        , MonadUnify unifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Ac.TermWrapper normalized valueWrapper
        , Traversable valueWrapper
        , Unparse variable
        )
    => Map.Map variable variable
    -> Sort
    -> Builtin.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
    -> Builtin.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
    -> MaybeT unifier (Predicate variable)
matchAc
    quantifiedVariables
    acSort
    Builtin.NormalizedAc
        { elementsWithVariables = varElems1
        , concreteElements      = concrete1
        , opaque                = varOpaque1
        }
    Builtin.NormalizedAc
        { elementsWithVariables = []
        , concreteElements      = concrete2
        , opaque                = []
        }
  | length varOpaque1 <= 1 = do
    let intersection
            :: Map.Map
                (TermLike Concrete)
                ( valueWrapper (TermLike variable)
                , valueWrapper (TermLike variable)
                )
        intersection = Map.intersectionWith (,) concrete1 concrete2
        remainder = Map.toList $ Map.difference concrete2 concrete1
    Monad.guard $ length remainder + length concrete1 == length concrete2
    Monad.guard $ length remainder >= length varElems1

    variableMatches <-
        fmap Foldable.fold
            . traverse matchElements
            $ zip varElems1 remainder

    intersectionMatches <-
        fmap Foldable.fold
            . traverse matchWrapped
            $ Map.elems intersection

    let elementMatches = variableMatches <> intersectionMatches

    let setRemainder = drop (length varElems1) remainder
    case (varOpaque1, setRemainder) of
        ([]   , []) -> pure elementMatches
        ([set], _ ) -> do
            tools <- Simplifier.askMetadataTools
            let subset =
                    Ac.asInternalConcrete tools acSort
                        $ Map.fromList setRemainder
            setsMatches <- match quantifiedVariables set subset
            pure $ elementMatches <> setsMatches
        _ -> nothing
  where
    matchElements
        ::  ( (TermLike variable, valueWrapper (TermLike variable))
            , (TermLike Concrete, valueWrapper (TermLike variable))
            )
        -> MaybeT unifier (Predicate variable)
    matchElements
        ((variableKey, variableValue), (concreteKey, concreteValue) )
      = do
        keyUnifier <-
            match quantifiedVariables variableKey (fromConcrete concreteKey)
        wrappedValueUnifier <- matchWrapped (variableValue, concreteValue)
        return (keyUnifier <> wrappedValueUnifier)

    matchWrapped
        ::  ( valueWrapper (TermLike variable)
            , valueWrapper (TermLike variable)
            )
        -> MaybeT unifier (Predicate variable)
    matchWrapped (variableValue, concreteValue) = do
        wrappedValueUnifier <-
            case Builtin.acExactZip variableValue concreteValue of
                Nothing -> error "Cannot pair ac values"
                Just zipped ->
                    traverse (uncurry (match quantifiedVariables)) zipped
        return (Foldable.fold wrappedValueUnifier)
matchAc _ _ _ _ = nothing
