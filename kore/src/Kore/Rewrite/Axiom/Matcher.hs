{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.Axiom.Matcher (
    MatchingVariable,
    MatchResult,
    patternMatch,
) where

import Control.Lens qualified as Lens
import Data.Align qualified as Align (
    align,
 )
import Data.Bifunctor qualified as Bifunctor
import Data.Functor.Foldable qualified as Recursive
import Data.Generics.Product
import Data.HashMap.Strict qualified as HashMap
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.PQueue.Min qualified as MinQueue
import Data.PQueue.Min (
    MinQueue,
 )
import Data.Sequence qualified as Seq
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Data.These (
    These (..),
 )
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import Kore.Builtin.AssociativeCommutative qualified as Ac
import Kore.Builtin.List qualified as List
import Kore.Internal.InternalList
import Kore.Internal.InternalMap hiding (
    Element,
    NormalizedAc,
    Value,
 )
import Kore.Internal.InternalSet hiding (
    Element,
    NormalizedAc,
    Value,
 )
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.NormalizedAc qualified as Builtin (
    Element,
    NormalizedAc,
    Value,
 )
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.MatcherData
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.InjSimplifier as InjSimplifier
import Kore.Simplify.Overloading (
    OverloadingResolution (..),
    flipResult,
    unifyOverloadingCommonOverload,
    unifyOverloadingVsOverloaded,
 )
import Kore.Simplify.Overloading qualified as Overloading (
    MatchResult (..),
 )
import Kore.Simplify.Simplify (
    Simplifier,
 )
import Kore.Simplify.Simplify qualified as Simplifier
import Kore.Substitute
import Kore.Unparser (
    unparseToText,
 )
import Pair
import Prelude.Kore

-- * Matching

{- | Match a TermLike against a pattern as represented by another TermLike.
 -
 - Unlike unification, pattern matching is not bidirectional. Variables may
 - appear in the term being matched, but they will not be unified with the
 - pattern, and are treated as if they were constants.
 -
 - At a high level, the pattern match algorithm maintains two lists. The first
 - list contains pairs of patterns and terms to match on immediately, and is
 - initialized with the initial pattern and term. The second list contains
 - pairs of map or set patterns and terms to be matched on on a deferred basis
 - after other matching finishes. Matching proceeds by popping a pattern and
 - a term off the first list, processing it, and performing one of several
 - actions:
 -
 - * failing matching, indicating pattern matching doesn't succeed and
 -   returning immediately.
 - * discharging it, indicating that matching locally succeeds and removing it
 -   from the list
 - * binding a variable to a term by adding it to the current substitution, and
 -   removing it from the list
 - * decomposing it into one or more subpatterns and subterms and adding them
 -   to the list
 - * deferring it by moving it to the second list if it is a map or set pattern
 - * some combination of the above
 -
 - Once the first list is empty, we remove one map or set pattern and term from
 - the second list and perform AC matching. This will perform some combination
 - of the above actions, potentially adding new elements to the first list.
 -
 - The algorithm then repeats this entire process until either matching fails
 - or both lists are empty, at which time matching succeeds with the
 - substitution that was accumulated.
-
-}
patternMatch ::
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Simplifier (Either Text (MatchResult RewritingVariableName))
patternMatch sideCondition pat subject =
    patternMatch' sideCondition [MatchItem pat subject [] Set.empty] MinQueue.empty MultiAnd.top Map.empty

data MatchItem = MatchItem (TermLike RewritingVariableName) (TermLike RewritingVariableName) [(SomeVariable RewritingVariableName, SomeVariable RewritingVariableName)] (Set (SomeVariableName RewritingVariableName))
    deriving stock (Eq)

type Element normalized =
    Builtin.Element normalized (TermLike RewritingVariableName)

type Value normalized =
    Builtin.Value normalized (TermLike RewritingVariableName)

type NormalizedAc normalized =
    Builtin.NormalizedAc normalized Key (TermLike RewritingVariableName)

needs ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Bool
needs (InternalSet_ s) term = needsAc (builtinAcChild s) term
needs (InternalMap_ m) term = needsAc (builtinAcChild m) term
needs _ _ = False

needsAc ::
    forall normalized.
    AcWrapper normalized =>
    normalized Key (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName ->
    Bool
needsAc collection term =
    not $ Set.disjoint (FreeVariables.toSet abstractFreeVars) $ FreeVariables.toSet $ freeVariables term
  where
    abstractKeys :: [TermLike RewritingVariableName]
    abstractKeys = getSymbolicKeysOfAc collection
    abstractFreeVars :: FreeVariables RewritingVariableName
    abstractFreeVars = foldMap freeVariables abstractKeys

instance Ord MatchItem where
    compare a@(MatchItem pat1 subject1 bound1 set1) b@(MatchItem pat2 subject2 bound2 set2) =
        if a == b then EQ else
        if pat1 `needs` pat2 then GT else
        if pat2 `needs` pat1 then LT else
        compare (pat1, subject1, bound1, set1) (pat2, subject2, bound2, set2)

finalizeSubst ::
    Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName) ->
    Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName)
finalizeSubst subst = Map.filterWithKey go subst
  where
    go k (Var_ v) = k /= variableName v
    go _ _ = True

patternMatch' ::
    SideCondition RewritingVariableName ->
    [MatchItem] ->
    MinQueue MatchItem ->
    MultiAnd (Predicate RewritingVariableName) ->
    Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName) ->
    Simplifier (Either Text (MatchResult RewritingVariableName))
patternMatch' _ [] queue predicate subst | MinQueue.null queue = return $ Right (Predicate.fromMultiAnd predicate, finalizeSubst subst)
patternMatch' sideCondition [] queue predicate subst = do
    injSimplifier <- Simplifier.askInjSimplifier
    let pat' = renormalizeBuiltins $ InjSimplifier.normalize injSimplifier $ substitute subst pat
    case (pat', subject) of
        (InternalMap_ map1, InternalMap_ map2) ->
            matchNormalizedAc decomposeList unwrapMapValue unwrapMapElement (wrapMap map2) (unwrapAc $ builtinAcChild map1) (unwrapAc $ builtinAcChild map2)
        (InternalSet_ set1, InternalSet_ set2) ->
            matchNormalizedAc decomposeList unwrapSetValue unwrapSetElement (wrapSet set2) (unwrapAc $ builtinAcChild set1) (unwrapAc $ builtinAcChild set2)
        _ -> error "error in matching algorithm: unexpected deferred term"
  where
    (MatchItem pat subject boundVars boundSet, rest) = MinQueue.deleteFindMin queue 

    decomposeList ::
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    decomposeList l =
        let l' = map (\(p, s) -> MatchItem p s boundVars boundSet) l
         in patternMatch' sideCondition l' rest predicate $ Map.foldl' processSubst subst subst

    processSubst ::
        Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName) ->
        TermLike RewritingVariableName ->
        Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName)
    processSubst subst' term =
        let vars = FreeVariables.toList $ freeVariables term
            newSubst = foldMap (\var -> Map.singleton (variableName var) (mkVar var)) vars
         in subst' <> newSubst

    wrapSet ::
        InternalAc Key NormalizedSet (TermLike RewritingVariableName) ->
        NormalizedAc NormalizedSet ->
        TermLike RewritingVariableName
    wrapSet set2 unwrapped =
        set2
            & Lens.set (field @"builtinAcChild") (wrapAc unwrapped)
            & mkInternalSet
    wrapMap ::
        InternalAc Key NormalizedMap (TermLike RewritingVariableName) ->
        NormalizedAc NormalizedMap ->
        TermLike RewritingVariableName
    wrapMap map2 unwrapped =
        map2
            & Lens.set (field @"builtinAcChild") (wrapAc unwrapped)
            & mkInternalMap

    unwrapSetValue ::
        [(Value NormalizedSet, Value NormalizedSet)] ->
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)]
    unwrapSetValue _ = []

    unwrapMapValue ::
        [(Value NormalizedMap, Value NormalizedMap)] ->
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)]
    unwrapMapValue vals = map (Bifunctor.bimap getMapValue getMapValue) vals

    unwrapSetElement ::
        Element NormalizedSet ->
        Element NormalizedSet ->
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)]
    unwrapSetElement elem1 elem2 = [(getSetElement elem1, getSetElement elem2)]

    unwrapMapElement ::
        Element NormalizedMap ->
        Element NormalizedMap ->
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)]
    unwrapMapElement elem1 elem2 =
        let (key1, val1) = getMapElement elem1
            (key2, val2) = getMapElement elem2
         in [(key1, key2), (val1, val2)]
patternMatch' sideCondition ((MatchItem pat subject boundVars boundSet) : rest) deferred predicate subst = do
    tools <- Simplifier.askMetadataTools
    injSimplifier <- Simplifier.askInjSimplifier
    overloadSimplifier <- Simplifier.askOverloadSimplifier
    let InjSimplifier{matchInjs, evaluateInj} = injSimplifier
    case (pat, subject) of
        (Var_ var1, Var_ var2) | isFree var1, var1 == var2 -> discharge
        (ElemVar_ var1, _) | isFree (inject var1), isFunctionPattern subject -> bind (inject var1) subject
        (SetVar_ var1, _) | isFree (inject var1) -> bind (inject var1) subject
        (Var_ var1, Var_ var2) | not $ isFree var1, var1 `isBoundToSameAs` var2 -> discharge
        (StringLiteral_ str1, StringLiteral_ str2) -> if str1 == str2 then discharge else failMatch "distinct string literals"
        (InternalInt_ int1, InternalInt_ int2) -> if int1 == int2 then discharge else failMatch "distinct builtin integers"
        (InternalBool_ bool1, InternalBool_ bool2) -> if bool1 == bool2 then discharge else failMatch "distinct builtin booleans"
        (InternalString_ string1, InternalString_ string2) -> if string1 == string2 then discharge else failMatch "distinct builtin strings"
        (InternalBytes_ _ bytes1, InternalBytes_ _ bytes2) -> if bytes1 == bytes2 then discharge else failMatch "distinct builtin bytes"
        (Endianness_ symbol1, Endianness_ symbol2) -> if symbol1 == symbol2 then discharge else failMatch "distinct endianness"
        (Signedness_ symbol1, Signedness_ symbol2) -> if symbol1 == symbol2 then discharge else failMatch "distinct signedness"
        (DV_ _ dv1, DV_ _ dv2) -> if dv1 == dv2 then discharge else failMatch "distinct domain values"
        (Bottom_ _, Bottom_ _) -> discharge
        (Top_ _, Top_ _) -> discharge
        (Ceil_ _ _ term1, Ceil_ _ _ term2) -> decompose term1 term2
        (Equals_ _ _ term11 term12, Equals_ _ _ term21 term22) -> decomposeTwo term11 term21 term12 term22
        (And_ _ term1 term2, _) -> decomposeTwo term1 subject term2 subject
        (Forall_ _ variable1 term1, Forall_ _ variable2 term2) -> decomposeBinder (inject variable1) term1 (inject variable2) term2
        (Exists_ _ variable1 term1, Exists_ _ variable2 term2) -> decomposeBinder (inject variable1) term1 (inject variable2) term2
        (App_ symbol1 children1, App_ symbol2 children2) -> if symbol1 == symbol2 then decomposeList (zip children1 children2) else failMatch $ "distinct application symbols: " <> (unparseToText symbol1) <> ", " <> (unparseToText symbol2)
        (Inj_ inj1, Inj_ inj2) | Just unifyData <- matchInjs inj1 inj2 ->
            case unifyData of
                UnifyInjDirect _ -> decompose (injChild inj1) (injChild inj2)
                UnifyInjSplit InjPair{inj1 = firstInj} ->
                    if injFrom firstInj == injFrom inj1
                        then decompose (injChild inj1) (evaluateInj inj2{injTo = injFrom inj1})
                        else decompose (evaluateInj inj1{injTo = injFrom inj2}) (injChild inj2)
                UnifyInjDistinct _ -> failMatch "distinct injections"
        (Inj_ inj@Inj{injChild = App_ firstHead firstChildren}, secondTerm@(App_ secondHead _))
            | Just unifyData <-
                unifyOverloadingVsOverloaded
                    overloadSimplifier
                    secondHead
                    secondTerm
                    (Application firstHead firstChildren)
                    inj{injChild = ()} ->
                decomposeOverload $ flipResult unifyData
        (firstTerm@(App_ firstHead _), Inj_ inj@Inj{injChild = App_ secondHead secondChildren})
            | Just unifyData <-
                unifyOverloadingVsOverloaded
                    overloadSimplifier
                    firstHead
                    firstTerm
                    (Application secondHead secondChildren)
                    inj{injChild = ()} ->
                decomposeOverload unifyData
        (Inj_ inj1@Inj{injChild = App_ firstHead firstChildren}, Inj_ Inj{injChild = App_ secondHead secondChildren})
            | Just unifyData <-
                unifyOverloadingCommonOverload
                    overloadSimplifier
                    (Application firstHead firstChildren)
                    (Application secondHead secondChildren)
                    inj1{injChild = ()} ->
                decomposeOverload unifyData
        (_, _) | Just True <- List.isListSort tools sort ->
            case (List.normalize pat, List.normalize subject) of
                (Var_ var1, Var_ var2) | var1 == var2 -> discharge
                (ElemVar_ var1, _) | isFunctionPattern subject -> bind (inject var1) subject
                (SetVar_ var1, _) -> bind (inject var1) subject
                (InternalList_ InternalList{internalListChild = l1}, InternalList_ InternalList{internalListChild = l2}) ->
                    if length l1 == length l2
                        then decomposeList $ zip (toList l1) (toList l2)
                        else failMatch "list lengths are not equal"
                (App_ symbol [InternalList_ InternalList{internalListChild = l1}, var@(ElemVar_ _)], InternalList_ InternalList{internalListChild = l2})
                    | List.isSymbolConcat symbol ->
                        if length l1 <= length l2
                            then
                                let l2' = Seq.drop (length l1) l2
                                 in decomposeList $ (var, List.asInternal tools sort l2') : zip (toList l1) (toList (Seq.take (length l1) l2))
                            else failMatch "subject list is too short"
                (App_ symbol [var@(ElemVar_ _), InternalList_ InternalList{internalListChild = l1}], InternalList_ InternalList{internalListChild = l2})
                    | List.isSymbolConcat symbol ->
                        if length l1 <= length l2
                            then
                                let l2' = Seq.take (length l2 - length l1) l2
                                 in decomposeList $ (var, List.asInternal tools sort l2') : zip (toList l1) (toList (Seq.drop (length l2 - length l1) l2))
                            else failMatch "subject list is too short"
                _ -> failMatch "unimplemented list matching case"
        (InternalMap_ _, InternalMap_ _) ->
            defer
        (InternalSet_ _, InternalSet_ _) ->
            defer
        _ -> failMatch "unimplemented matching case"
  where
    sort = termLikeSort pat

    discharge ::
        Simplifier (Either Text (MatchResult RewritingVariableName))
    ~discharge = patternMatch' sideCondition rest deferred predicate subst

    bind ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    bind var term =
        let varName = variableName var
            freeVars = FreeVariables.toNames (freeVariables term)
         in if not $ Set.disjoint freeVars boundSet
                then failMatch "bound variable would escape binder"
                else case Map.lookup varName subst of
                    Nothing -> patternMatch' sideCondition rest deferred (isTermDefined var term) (Map.insert (variableName var) term subst)
                    Just binding -> if binding == term then patternMatch' sideCondition rest deferred predicate subst else failMatch "nonlinear matching fails equality test"

    isTermDefined ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        MultiAnd (Predicate RewritingVariableName)
    isTermDefined var term
        | SideCondition.isDefined sideCondition term || isSetVariable var = predicate
        | otherwise = (predicate <> MultiAnd.make [makeCeilPredicate term])

    decompose ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    decompose term1 term2 = patternMatch' sideCondition ((MatchItem term1 term2 boundVars boundSet) : rest) deferred predicate subst

    defer ::
        Simplifier (Either Text (MatchResult RewritingVariableName))
    ~defer = patternMatch' sideCondition rest (MinQueue.insert (MatchItem pat subject boundVars boundSet) deferred) predicate subst

    decomposeTwo ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    decomposeTwo term11 term21 term12 term22 = patternMatch' sideCondition ((MatchItem term11 term21 boundVars boundSet) : (MatchItem term12 term22 boundVars boundSet) : rest) deferred predicate subst

    decomposeList ::
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    decomposeList l =
        let l' = map (\(p, s) -> MatchItem p s boundVars boundSet) l
         in patternMatch' sideCondition (l' ++ rest) deferred predicate subst

    decomposeBinder ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        Simplifier (Either Text (MatchResult RewritingVariableName))
    decomposeBinder var1 term1 var2 term2 = patternMatch' sideCondition ((MatchItem term1 term2 ((var1, var2) : boundVars) (Set.insert (variableName var2) boundSet)) : rest) deferred predicate subst

    decomposeOverload (Overloading.Resolution (Simple (Pair term1 term2))) = decompose term1 term2
    decomposeOverload _ = failMatch "unsupported overload case in matching"

    isFree ::
        SomeVariable RewritingVariableName ->
        Bool
    isFree var = not $ any ((== var) . fst) boundVars

    isBoundToSameAs var1 var2 =
        case find ((== var1) . fst) boundVars of
            Nothing -> undefined
            Just (_, bound) -> var2 == bound

failMatch ::
    Text ->
    Simplifier (Either Text (MatchResult RewritingVariableName))
failMatch msg = return $ Left msg

type MatchingVariable variable = InternalVariable variable

type PushList a = [(a, a)] -> Simplifier (Either Text (MatchResult RewritingVariableName))

matchNormalizedAc ::
    forall normalized.
    ( AcWrapper normalized
    ) =>
    PushList (TermLike RewritingVariableName) ->
    ([(Value normalized, Value normalized)] -> [(TermLike RewritingVariableName, TermLike RewritingVariableName)]) ->
    (Element normalized -> Element normalized -> [(TermLike RewritingVariableName, TermLike RewritingVariableName)]) ->
    (NormalizedAc normalized -> TermLike RewritingVariableName) ->
    NormalizedAc normalized ->
    NormalizedAc normalized ->
    Simplifier (Either Text (MatchResult RewritingVariableName))
matchNormalizedAc decomposeList unwrapValues unwrapElementToTermLike wrapTermLike normalized1 normalized2
    -- Case for when all symbolic elements in normalized1 appear in normalized2:
    | [] <- excessAbstract1 =
        -- All concrete elements in normalized1 appear in normalized2
        if not $ null excessConcrete1
            then failMatch "AC collection missing concrete elements"
            else case opaque1 of
                -- Without opaques and syntactically equal
                [] ->
                    if not (null opaque2) || not (null excessConcrete2) || not (null excessAbstract2) then failMatch "AC collection without opaque terms has excess elements" else decomposeList $ unwrapValues $ concrete12 ++ abstractMerge
                [frame1]
                    -- One opaque each, rest are syntactically equal
                    | null excessAbstract2
                      , null excessConcrete2
                      , [frame2] <- opaque2 ->
                        decomposeList $ (frame1, frame2) : unwrapValues (concrete12 ++ abstractMerge)
                    -- Match singular opaque1 with excess part of normalized2
                    | otherwise ->
                        let normalized2' =
                                wrapTermLike
                                    normalized2
                                        { concreteElements = excessConcrete2
                                        , elementsWithVariables = excessAbstract2
                                        }
                         in decomposeList $ (frame1, normalized2') : unwrapValues (concrete12 ++ abstractMerge)
                frames1
                    -- Opaque parts are equivalent, rest is syntactically equal
                    | null excessAbstract2
                      , null excessConcrete2
                      , frames2 <- opaque2
                      , length frames1 == length frames2 ->
                        decomposeList $ unwrapValues (concrete12 ++ abstractMerge) ++ zip opaque1ACs opaque2ACs
                    | otherwise -> failMatch "unimplemented ac collection case"
    -- Case for AC iteration:
    -- Normalized1 looks like K |-> V M:Map
    | [element1] <- abstract1
      , [frame1] <- opaque1
      , null concrete1 = do
        let (key1, value1) = unwrapElement element1
        case lookupSymbolicKeyOfAc key1 normalized2 of
            -- If K in_keys(normalized2)
            Just value2 ->
                let normalized2' =
                        wrapTermLike $
                            removeSymbolicKeyOfAc key1 normalized2
                 in decomposeList $ (frame1, normalized2') : unwrapValues [(value1, value2)]
            Nothing ->
                case (headMay . HashMap.toList $ concrete2, headMay abstract2) of
                    -- Select first concrete element of normalized2, concrete2
                    -- Match K |-> V with concrete2
                    -- Match M with remove(normalized2, concrete2)
                    (Just concreteElement2, _) ->
                        let liftedConcreteElement2 =
                                Bifunctor.first (from @Key) concreteElement2
                                    & wrapElement
                            (key2, _) = concreteElement2
                            normalized2' =
                                wrapTermLike $
                                    removeConcreteKeyOfAc key2 normalized2
                         in decomposeList $ (frame1, normalized2') : unwrapElementToTermLike element1 liftedConcreteElement2
                    -- Select first symbolic element of normalized2, symbolic2
                    -- Match K |-> V with symbolic2
                    -- Match M with remove(normalized2, symbolic2)
                    (_, Just abstractElement2) ->
                        let (key2, _) = unwrapElement abstractElement2
                            normalized2' =
                                wrapTermLike $
                                    removeSymbolicKeyOfAc key2 normalized2
                         in decomposeList $ (frame1, normalized2') : unwrapElementToTermLike element1 abstractElement2
                    _ -> failMatch "unimplemented ac collection case"
    -- Case for ACs which are structurally equal:
    | length excessAbstract1 == length excessAbstract2
      , length concrete1 == length concrete2
      , length opaque1 == length opaque2 =
        decomposeList $ unwrapValues (abstractMerge ++ concrete12) ++ unwrapElements (zip excessAbstract1 excessAbstract2) ++ (zip opaque1ACs opaque2ACs)
    | otherwise = failMatch "unimplemented ac collection case"
  where
    abstract1 = elementsWithVariables normalized1
    concrete1 = concreteElements normalized1
    opaque1 = opaque normalized1
    opaque1ACs = wrapTermLike . toSingleOpaqueElem <$> opaque1
    abstract2 = elementsWithVariables normalized2
    concrete2 = concreteElements normalized2
    opaque2 = opaque normalized2
    opaque2ACs = wrapTermLike . toSingleOpaqueElem <$> opaque2

    excessConcrete1 = HashMap.difference concrete1 concrete2
    excessConcrete2 = HashMap.difference concrete2 concrete1
    concrete12 = HashMap.elems $ HashMap.intersectionWith (,) concrete1 concrete2

    unwrapElements = concatMap $ uncurry unwrapElementToTermLike

    IntersectionDifference
        { intersection = abstractMerge
        , excessFirst = excessAbstract1
        , excessSecond = excessAbstract2
        } = abstractIntersectionMerge abstract1 abstract2

    abstractIntersectionMerge ::
        [Element normalized] ->
        [Element normalized] ->
        IntersectionDifference
            (Element normalized)
            (Value normalized, Value normalized)
    abstractIntersectionMerge first second =
        keyBasedIntersectionDifference
            elementMerger
            (toMap first)
            (toMap second)
      where
        toMap ::
            [Element normalized] ->
            Map (TermLike RewritingVariableName) (Element normalized)
        toMap elements =
            let elementMap =
                    Map.fromList
                        ( map
                            (\value -> (elementKey value, value))
                            elements
                        )
             in if length elementMap == length elements
                    then elementMap
                    else error "Invalid map: duplicated keys."
        elementKey ::
            Element normalized ->
            TermLike RewritingVariableName
        elementKey = fst . unwrapElement
        elementMerger ::
            Element normalized ->
            Element normalized ->
            (Value normalized, Value normalized)
        elementMerger = (,) `on` (snd . unwrapElement)

data IntersectionDifference a b = IntersectionDifference
    { intersection :: ![b]
    , excessFirst :: ![a]
    , excessSecond :: ![a]
    }
    deriving stock (Show)

emptyIntersectionDifference :: IntersectionDifference a b
emptyIntersectionDifference =
    IntersectionDifference
        { intersection = []
        , excessFirst = []
        , excessSecond = []
        }

keyBasedIntersectionDifference ::
    forall a b k.
    Ord k =>
    (a -> a -> b) ->
    Map k a ->
    Map k a ->
    IntersectionDifference a b
keyBasedIntersectionDifference merger firsts seconds =
    foldl'
        helper
        emptyIntersectionDifference
        (Map.elems $ Align.align firsts seconds)
  where
    helper ::
        IntersectionDifference a b ->
        These a a ->
        IntersectionDifference a b
    helper
        result@IntersectionDifference{excessFirst}
        (This first) =
            result{excessFirst = first : excessFirst}
    helper
        result@IntersectionDifference{excessSecond}
        (That second) =
            result{excessSecond = second : excessSecond}
    helper
        result@IntersectionDifference{intersection}
        (These first second) =
            result{intersection = merger first second : intersection}

-- | Renormalize builtin types after substitution.
renormalizeBuiltins ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
renormalizeBuiltins =
    Recursive.fold $ \base@(attrs :< termLikeF) ->
        let bottom' = mkBottom (termSort attrs)
         in case termLikeF of
                InternalMapF internalMap ->
                    Lens.traverseOf (field @"builtinAcChild") Ac.renormalize internalMap
                        & maybe bottom' mkInternalMap
                InternalSetF internalSet ->
                    Lens.traverseOf (field @"builtinAcChild") Ac.renormalize internalSet
                        & maybe bottom' mkInternalSet
                _ -> Recursive.embed base
