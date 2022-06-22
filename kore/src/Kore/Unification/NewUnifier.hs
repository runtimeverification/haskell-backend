{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Unification algorithm based on "Competing for the AC-Unification Race"
(https://doi.org/10.1007/BF00881905) and "Combining Unification Algorithms"
(https://doi.org/10.1006/jsco.1993.1066) by Alexandre Boudet. We have taken
some adjustments for ACU unification from the Maude codebase as well.
(https://github.com/SRI-CSL/Maude/blob/master/src/ACU_Theory/ACU_UnificationSubproblem2.cc)

The algorithm for ACU unification has been adapted specifically for K, in
particular based on the assumption that all ACU unification problems will have
no uninterpreted functions and each map or set element will consist of a single
free constructor representing a single element operating over a sort containing
a single ACU constructor, concatenation.
-}
module Kore.Unification.NewUnifier (
    unifyTerms,
    unifiedTermAnd,
    -- exported for debugging and testing
    solveDiophantineEquations,
    allSuitableSolutions',
    combine,
) where

import Data.DecisionDiagram.BDD (
    AscOrder,
    BDD,
    (.&&.),
    (.||.),
 )
import Data.DecisionDiagram.BDD qualified as BDD
import Data.Either (
    lefts,
    rights,
 )
import Data.HashMap.Strict qualified as HashMap
import Data.IntMap (
    IntMap,
 )
import Data.IntMap qualified as IntMap
import Data.IntSet (
    IntSet,
 )
import Data.IntSet qualified as IntSet
import Data.List (
    elemIndex,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Matrix (
    Matrix,
 )
import Data.Matrix qualified as Matrix
import Data.Maybe (
    fromJust,
 )
import Data.MultiSet (
    MultiSet,
 )
import Data.MultiSet qualified as MultiSet
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Data.Vector (
    Vector,
    (!),
 )
import Data.Vector qualified as Vector
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Builtin.AssociativeCommutative qualified as Ac
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.KEqual (
    iteKey,
 )
import Kore.Builtin.Map (
    isMapSort,
 )
import Kore.Builtin.Set (
    isSetSort,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.Condition (
    Condition,
    Conditional (..),
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.InternalMap (
    InternalMap,
    NormalizedMap (..),
    getMapElement,
    getMapValue,
 )
import Kore.Internal.InternalSet (
    InternalSet,
    NormalizedSet (..),
    getSetElement,
 )
import Kore.Internal.NormalizedAc (
    InternalAc (..),
    NormalizedAc (..),
    unwrapAc,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeEqualsPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.Symbol qualified as Symbol
import Kore.Internal.TermLike
import Kore.Log.DebugUnification (
    whileDebugUnification,
    debugUnificationSolved,
 )
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.ExpandAlias (
    UnifyExpandAlias (..),
    matchExpandAlias,
 )
import Kore.Simplify.InjSimplifier (
    InjPair (..),
    InjSimplifier (..),
    UnifyInj (..),
 )
import Kore.Simplify.OverloadSimplifier (
    OverloadSimplifier (..),
 )
import Kore.Simplify.Overloading (
    MatchResult (..),
    Narrowing (..),
    OverloadingResolution (..),
    unifyOverloadingCommonOverload,
    unifyOverloadingInjVsVariable,
    unifyOverloadingVsOverloaded,
    unifyOverloadingVsOverloadedVariable,
 )
import Kore.Simplify.Simplify (
    askInjSimplifier,
    askMetadataTools,
    askOverloadSimplifier,
    simplifyTerm,
 )
import Kore.Substitute
import Kore.Unification.SubstitutionNormalization
import Kore.Unification.Unify
import Kore.Variables.Fresh (
    refreshVariable,
 )
import Logic
import Pair
import Prelude.Kore

data AcTerm = AcTerm
    { acElements :: [SomeVariable RewritingVariableName]
    , acSort :: Sort
    , elementVars :: Set (SomeVariableName RewritingVariableName)
    }
    deriving stock (Show, Eq)
data AcEquation = AcEquation AcTerm AcTerm
    deriving stock (Show, Eq)

data AcCollection = AcCollection
    { elements :: Set (TermLike RewritingVariableName)
    , functions :: MultiSet (TermLike RewritingVariableName)
    , variables :: MultiSet (SomeVariable RewritingVariableName)
    }
    deriving stock (Show)

data Binding
    = Free (TermLike RewritingVariableName)
    | Ac AcTerm
    deriving stock (Show, Eq)

fromFree :: Binding -> TermLike RewritingVariableName
fromFree (Free a) = a
fromFree (Ac _) = error "fromFree"

fromAc :: Binding -> AcTerm
fromAc (Ac a) = a
fromAc (Free _) = error "fromAc"

isFree :: Binding -> Bool
isFree (Free _) = True
isFree (Ac _) = False

isAc :: Binding -> Bool
isAc (Ac _) = True
isAc (Free _) = False

isVar :: TermLike RewritingVariableName -> Bool
isVar (ElemVar_ _) = True
isVar _ = False

elemVar :: TermLike RewritingVariableName -> SomeVariable RewritingVariableName
elemVar (ElemVar_ var) = inject var
elemVar _ = error "elemVar"

combine :: [[a]] -> [[a]]
combine [] = []
combine [x] = map (: []) x
combine (x : xs) =
    let combined = combine xs
     in [a : as | a <- x, as <- combined]

union :: HasCallStack => Ord k => Map k v -> Map k v -> Map k v
union m1 m2 = Map.unionWith (error "duplicate binding") m1 m2

varRep ::
    HasCallStack =>
    [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)] ->
    Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName) ->
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    Set (SomeVariableName RewritingVariableName) ->
    ([(TermLike RewritingVariableName, TermLike RewritingVariableName)], Map (SomeVariable RewritingVariableName) Binding)
varRep solution improper eqs origVars =
    case getImproperBinding solution of
        Nothing -> (eqs, Map.map Free $ foldr union improper solution)
        Just (x, t, solution') ->
            let replacedValues = map (Map.map (substitute (Map.singleton (variableName x) t))) solution'
                (newEqs, replacedKeys) = substituteInKeys x t replacedValues
             in varRep replacedKeys (Map.insert x t improper) (eqs ++ newEqs) origVars

substituteInKeys ::
    SomeVariable RewritingVariableName ->
    TermLike RewritingVariableName ->
    [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)] ->
    ([(TermLike RewritingVariableName, TermLike RewritingVariableName)], [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)])
substituteInKeys x s solution =
    foldr substitute' ([], []) solution
  where
    substitute' subst (eqs, solution') =
        case Map.lookup x subst of
            Nothing -> (eqs, subst : solution')
            Just t -> ((s, t) : eqs, Map.delete x subst : solution')

getImproperBinding ::
    [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)] ->
    Maybe (SomeVariable RewritingVariableName, TermLike RewritingVariableName, [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)])
getImproperBinding solution = go solution []
  where
    go [] _ = Nothing
    go (m : hd) tl =
        case getImproperBinding' m of
            Nothing -> go hd (m : tl)
            Just (x, y, rest) -> Just (x, y, tl ++ (rest : hd))
    getImproperBinding' m =
        let improper = Map.filter isVar m
         in if Map.null improper
                then Nothing
                else
                    let (k, v) = Map.findMin improper
                     in Just (k, v, Map.delete k m)

combineTheories ::
    MonadUnify unifier =>
    [[Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)]] ->
    Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName) ->
    Set (SomeVariableName RewritingVariableName) ->
    unifier ([(TermLike RewritingVariableName, TermLike RewritingVariableName)], Map (SomeVariable RewritingVariableName) Binding)
combineTheories acBindings freeBindings origVars = do
    let withoutPureImproperBindings = map (map preprocessTheory) acBindings
        combinations = combine withoutPureImproperBindings
    solution <- Logic.scatter combinations
    return $ varRep (freeBindings : solution) Map.empty [] origVars
  where
    preprocessTheory ::
        Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName) ->
        Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)
    preprocessTheory bindings = fst $ Map.foldrWithKey' preprocessBinding (Map.empty, Map.empty) bindings
    preprocessBinding ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        (Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName), Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName)) ->
        (Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName), Map (SomeVariableName RewritingVariableName) (TermLike RewritingVariableName))
    preprocessBinding key (ElemVar_ var) (accum, subst) =
        let substKey = variableName $ inject var
            substVal = mkElemVar $ fromJust $ retract key
         in case Map.lookup substKey subst of
                Nothing -> (Map.map (substitute (Map.singleton substKey substVal)) accum, Map.insert substKey substVal subst)
                Just substituted -> (Map.insert key substituted accum, subst)
    preprocessBinding key val (accum, subst) =
        (Map.insert key (substitute subst val) accum, subst)

unifiedTermAnd ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Condition RewritingVariableName ->
    TermLike RewritingVariableName
unifiedTermAnd p1 p2 condition =
    let Conditional{substitution} = condition
        normalized = Substitution.toMap substitution
        term1 = substitute normalized p1
        term2 = substitute normalized p2
    in mkAnd term1 term2

unifyTerms ::
    MonadUnify unifier =>
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    unifier (Condition RewritingVariableName)
unifyTerms first second sideCondition =
    let vars = Set.map variableName $ FreeVariables.toSet $ freeVariables (first, second)
     in unifyTerms' (termLikeSort first) sideCondition vars vars [(first, second)] Map.empty Condition.topCondition Map.empty

unifyTerms' ::
    forall unifier.
    MonadUnify unifier =>
    HasCallStack =>
    Sort ->
    SideCondition RewritingVariableName ->
    Set (SomeVariableName RewritingVariableName) ->
    Set (SomeVariableName RewritingVariableName) ->
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    Map (SomeVariable RewritingVariableName) Binding ->
    Condition RewritingVariableName ->
    Map Sort [AcEquation] ->
    unifier (Condition RewritingVariableName)
unifyTerms' rootSort _ origVars _ [] bindings constraints acEquations
    | Map.null acEquations = do
        let freeBindings = Map.map fromFree $ Map.filter isFree bindings
            (origBindings, acVarBindings) = Map.partitionWithKey isOrigVar freeBindings
            acVarSubst = Map.mapKeys variableName acVarBindings
            finalBindings = Map.map (substitute acVarSubst) origBindings
        case normalize finalBindings of
            Nothing -> empty
            Just normalization -> do
                let condition = Condition.fromNormalizationSimplified normalization
                    solution = Condition.andCondition condition constraints
                debugUnificationSolved (Pattern.fromCondition rootSort solution)
                return solution
  where
    isOrigVar :: SomeVariable RewritingVariableName -> a -> Bool
    isOrigVar v = const $ Set.member (variableName v) origVars
unifyTerms' rootSort sideCondition origVars vars [] bindings constraints acEquations = do
    tools <- askMetadataTools
    let (acSolutions, newVars) = Map.foldrWithKey' (solveAcEquations' tools) (Map.empty, vars) acEquations
        freeBindings = Map.map fromFree $ Map.filter isFree bindings
    (newEqs, newBindings) <- combineTheories (Map.elems acSolutions) freeBindings origVars
    unifyTerms' rootSort sideCondition origVars newVars newEqs newBindings constraints Map.empty
  where
    solveAcEquations' ::
        SmtMetadataTools Attribute.Symbol ->
        Sort ->
        [AcEquation] ->
        (Map Sort [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)], Set (SomeVariableName RewritingVariableName)) ->
        (Map Sort [Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)], Set (SomeVariableName RewritingVariableName))
    solveAcEquations' tools sort eqs (accum, vars') =
        let (solutions, newVars) = solveAcEquations tools bindings vars' sort eqs
         in (Map.insert sort solutions accum, newVars)
unifyTerms' rootSort sideCondition origVars vars ((first, second) : rest) bindings constraints acEquations =
    whileDebugUnification first second $ do
        tools <- askMetadataTools
        injSimplifier <- askInjSimplifier
        overloadSimplifier <- askOverloadSimplifier
        let InjSimplifier{matchInjs, evaluateInj} = injSimplifier
            OverloadSimplifier{isOverloaded} = overloadSimplifier
        case (first, second) of
            (_, _) | Just UnifyExpandAlias{term1, term2} <- matchExpandAlias first second -> decompose term1 term2
            (Bottom_ _, _) -> failUnify "Cannot unify bottom"
            (_, Bottom_ _) -> failUnify "Cannot unify bottom"
            (Top_ _, _) -> discharge
            (_, Top_ _) -> discharge
            (And_ _ term1 term2, _) -> decomposeList [(term1, second), (term2, second)]
            (_, And_ _ term1 term2) -> decomposeList [(first, term1), (first, term2)]
            (Or_ _ term1 term2, _) -> do
                term <- Logic.scatter [term1, term2]
                decompose term second
            (_, Or_ _ term1 term2) -> do
                term <- Logic.scatter [term1, term2]
                decompose first term
            (_, _) | first == second -> discharge
            (InternalInt_ _, InternalInt_ _) -> failUnify "Distinct integer domain values"
            (InternalBool_ _, InternalBool_ _) -> failUnify "Distinct Boolean domain values"
            (InternalString_ _, InternalString_ _) -> failUnify "Distinct string domain values"
            (DV_ _ _, DV_ _ _) -> failUnify "Distinct domain values"
            (StringLiteral_ _, StringLiteral_ _) -> failUnify "Distinct string literals"
            (InternalBytes_ _ _, InternalBytes_ _ _) -> failUnify "Distinct byte-string domain values"
            (Endianness_ _, Endianness_ _) -> failUnify "Distinct Endianness constructors"
            (Signedness_ _, Signedness_ _) -> failUnify "Distinct Signedness constructors"
            (ElemVar_ var1, ElemVar_ var2) -> bindVarToVar (inject var1) (inject var2)
            (ElemVar_ var1, _) | isFunctionPattern second -> bindVarToPattern (inject var1) second
            (_, ElemVar_ var2) | isFunctionPattern first -> bindVarToPattern (inject var2) first
            (App_ firstHead firstChildren, App_ secondHead secondChildren)
                | Symbol.isInjective firstHead
                  , firstHead == secondHead ->
                    decomposeList (zip firstChildren secondChildren)
            (App_ firstHead _, App_ secondHead _)
                | firstHead /= secondHead
                  , Symbol.isConstructor firstHead || isOverloaded firstHead
                  , Symbol.isConstructor secondHead || isOverloaded secondHead ->
                    failUnify
                        "Cannot unify different constructors or incompatible \
                        \sort injections"
            (Inj_ inj1, Inj_ inj2) | Just unifyData <- matchInjs inj1 inj2 ->
                case unifyData of
                    UnifyInjDirect _ -> decompose (injChild inj1) (injChild inj2)
                    UnifyInjSplit InjPair{inj1 = firstInj, inj2 = secondInj} ->
                        decompose (injChild firstInj) (evaluateInj secondInj{injTo = injFrom firstInj})
                    UnifyInjDistinct _ -> failUnify "Distinct sort injections"
            (Inj_ _, App_ secondHead _) | Symbol.isConstructor secondHead -> failUnify "Cannot unify sort injection with constructor"
            (App_ firstHead _, Inj_ _) | Symbol.isConstructor firstHead -> failUnify "Cannot unify sort injection with constructor"
            (Inj_ inj@Inj{injChild = App_ firstHead firstChildren}, secondTerm@(App_ secondHead _))
                | Just unifyData <-
                    unifyOverloadingVsOverloaded
                        overloadSimplifier
                        secondHead
                        secondTerm
                        (Application firstHead firstChildren)
                        inj{injChild = ()} ->
                    decomposeOverload unifyData
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
            (firstTerm@(App_ firstHead _), Inj_ inj@Inj{injChild = ElemVar_ secondVar})
                | Just unifyData <-
                    unifyOverloadingVsOverloadedVariable
                        overloadSimplifier
                        firstHead
                        firstTerm
                        secondVar
                        inj{injChild = ()} ->
                    decomposeOverload unifyData
            (Inj_ inj@Inj{injChild = ElemVar_ firstVar}, secondTerm@(App_ secondHead _))
                | Just unifyData <-
                    unifyOverloadingVsOverloadedVariable
                        overloadSimplifier
                        secondHead
                        secondTerm
                        firstVar
                        inj{injChild = ()} ->
                    decomposeOverload unifyData
            (Inj_ Inj{injChild = firstTerm@(App_ firstHead firstChildren)}, Inj_ inj@Inj{injChild = ElemVar_ secondVar})
                | Just unifyData <-
                    unifyOverloadingInjVsVariable
                        overloadSimplifier
                        (Application firstHead firstChildren)
                        secondVar
                        (FreeVariables.freeVariables firstTerm)
                        inj{injChild = ()} ->
                    decomposeOverload unifyData
            (Inj_ inj@Inj{injChild = ElemVar_ firstVar}, Inj_ Inj{injChild = secondTerm@(App_ secondHead secondChildren)})
                | Just unifyData <-
                    unifyOverloadingInjVsVariable
                        overloadSimplifier
                        (Application secondHead secondChildren)
                        firstVar
                        (FreeVariables.freeVariables secondTerm)
                        inj{injChild = ()} ->
                    decomposeOverload unifyData
            (App_ firstHead _, Inj_ _)
                | isOverloaded firstHead ->
                    failUnify "Cannot unify sort injection with overloaded symbol it does not overload with"
            (Inj_ _, App_ secondHead _)
                | isOverloaded secondHead ->
                    failUnify "Cannot unify sort injection with overloaded symbol it does not overload with"
            (Inj_ _, Inj_ _) -> failUnify "Distinct sort injections"
            (InternalMap_ map1, InternalMap_ map2) -> unifyMaps map1 map2
            (InternalMap_ map1, _) ->
                case Ac.toNormalized second of
                    Ac.Bottom -> failUnify "Duplicate elements in normalized map"
                    Ac.Normalized map2 -> unifyMaps map1 $ Ac.asInternalBuiltin tools sort map2
            (_, InternalMap_ map2) ->
                case Ac.toNormalized first of
                    Ac.Bottom -> failUnify "Duplicate elements in normalized map"
                    Ac.Normalized map1 -> unifyMaps (Ac.asInternalBuiltin tools sort map1) map2
            (_, _) | Just True <- isMapSort tools sort ->
                case (Ac.toNormalized first, Ac.toNormalized second) of
                    (Ac.Bottom, _) -> failUnify "Duplicate elements in normalized map"
                    (_, Ac.Bottom) -> failUnify "Duplicate elements in normalized map"
                    (Ac.Normalized map1, Ac.Normalized map2) ->
                        unifyMaps
                            (Ac.asInternalBuiltin tools sort map1)
                            (Ac.asInternalBuiltin tools sort map2)
            (InternalSet_ set1, InternalSet_ set2) -> unifySets set1 set2
            (InternalSet_ set1, _) ->
                case Ac.toNormalized second of
                    Ac.Bottom -> failUnify "Duplicate elements in normalized set"
                    Ac.Normalized set2 -> unifySets set1 $ Ac.asInternalBuiltin tools sort set2
            (_, InternalSet_ set2) ->
                case Ac.toNormalized first of
                    Ac.Bottom -> failUnify "Duplicate elements in normalized set"
                    Ac.Normalized set1 -> unifySets (Ac.asInternalBuiltin tools sort set1) set2
            (_, _) | Just True <- isSetSort tools sort ->
                case (Ac.toNormalized first, Ac.toNormalized second) of
                    (Ac.Bottom, _) -> failUnify "Duplicate elements in normalized set"
                    (_, Ac.Bottom) -> failUnify "Duplicate elements in normalized set"
                    (Ac.Normalized set1, Ac.Normalized set2) ->
                        unifySets
                            (Ac.asInternalBuiltin tools sort set1)
                            (Ac.asInternalBuiltin tools sort set2)
            -- in theory we could now implement these cases as simplification rules
            -- instead of unification cases, but unlike the other boolean operations,
            -- we can't actually express this rule in K because K does not yet support
            -- parametric rules and #if #then #else #fi is parametric.
            (App_ ite [condition, branch1, branch2], _)
                | Just iteKey == getHook (Symbol.symbolHook ite) ->
                    unifyIfThenElse condition branch1 branch2 second
            (_, App_ ite [condition, branch1, branch2])
                | Just iteKey == getHook (Symbol.symbolHook ite) ->
                    unifyIfThenElse condition branch1 branch2 first
            (_, _) | isFunctionPattern first -> trySubstDecompose
            (_, _) | isFunctionPattern second -> trySubstDecompose
            _ -> constrainEquals first second
  where
    sort = termLikeSort first

    discharge ::
        unifier (Condition RewritingVariableName)
    discharge = unifyTerms' rootSort sideCondition origVars vars rest bindings constraints acEquations

    failUnify ::
        Text ->
        unifier (Condition RewritingVariableName)
    failUnify message = debugUnifyBottomAndReturnBottom message first second

    decompose ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    decompose term1 term2 = unifyTerms' rootSort sideCondition origVars vars ((term1, term2) : rest) bindings constraints acEquations

    decomposeList ::
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
        unifier (Condition RewritingVariableName)
    decomposeList terms = unifyTerms' rootSort sideCondition origVars vars (terms ++ rest) bindings constraints acEquations

    constrain ::
        Predicate RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    constrain predicate = unifyTerms' rootSort sideCondition origVars vars rest bindings (Condition.andCondition constraints $ Condition.fromPredicate predicate) acEquations

    constrainEquals ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    constrainEquals p1 p2 = do
        let predicate = makeEqualsPredicate p1 p2
        constrain predicate

    bind ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    bind var term = unifyTerms' rootSort sideCondition origVars vars rest (Map.insert var (Free term) bindings) constraints acEquations

    binding var = Map.lookup var bindings

    bindVarToVar var1 var2 =
        if var1 == var2
            then discharge
            else case (binding var1, binding var2) of
                (Just (Free (ElemVar_ var1')), Just (Free (ElemVar_ var2'))) -> bindVarToVar (inject var1') (inject var2')
                (Just (Free (ElemVar_ var1')), _) -> bindVarToVar (inject var1') var2
                (_, Just (Free (ElemVar_ var2'))) -> bindVarToVar var1 (inject var2')
                (Nothing, _) -> 
                    let (var, term) = Substitution.normalOrder (var1, second)
                    in bind var term
                (_, Nothing) -> bind var2 first
                (Just (Free term1), Just (Free term2)) -> decompose term1 term2
                (Just (Ac term1), Just (Ac term2)) -> acDecompose term1 term2
                _ -> error "invalid free binding for AC sort"
    bindVarToPattern ::
        SomeVariable RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Condition RewritingVariableName)
    bindVarToPattern var term =
        case binding var of
            Nothing -> bind var term
            Just (Free (ElemVar_ boundVar)) -> bind (inject boundVar) term
            Just (Free boundVar) -> decompose boundVar term
            Just (Ac _) -> error "invalid free binding for AC sort"
    decomposeOverload (ClashResult _) = failUnify "Overloaded constructors do not unify with each other"
    decomposeOverload (Resolution (Simple (Pair term1 term2))) = decompose term1 term2
    decomposeOverload
        ( Resolution
                ( WithNarrowing
                        Narrowing
                            { narrowingSubst
                            , overloadPair = Pair term1 term2
                            }
                    )
            ) = unifyTerms' rootSort sideCondition origVars vars ((term1, term2) : rest) bindings (Condition.andCondition constraints narrowingSubst) acEquations

    trySubstDecompose = do
        (newFirst, firstConstraints) <- substAndSimplify constraints first
        (newSecond, secondConstraints) <- substAndSimplify firstConstraints second
        if newFirst /= first || newSecond /= second
            then unifyTerms' rootSort sideCondition origVars vars ((newFirst, newSecond) : rest) bindings secondConstraints acEquations
            else constrainEquals first second

    unifyIfThenElse condition branch1 branch2 other = do
        (bool, branch) <- Logic.scatter [(True, branch1), (False, branch2)]
        let newConstraints =
                Condition.andCondition constraints $
                    Condition.fromPredicate $
                        makeCeilPredicate $ mkAnd condition $ Bool.asInternal (termLikeSort condition) bool
        unifyTerms' rootSort sideCondition origVars vars ((branch, other) : rest) bindings newConstraints acEquations

    substAndSimplify ::
        Condition RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (TermLike RewritingVariableName, Condition RewritingVariableName)
    substAndSimplify constraints' term = do
        let substituted = substitute currentSubstitution term
        if substituted /= term
            then do
                pats <- simplifyTerm sideCondition substituted
                pat <- Logic.scatter pats
                let (term', condition) = Pattern.splitTerm pat
                return (term', Condition.andCondition constraints' condition)
            else return (term, constraints')

    currentSubstitution = Map.mapKeys variableName $ Map.map fromFree $ Map.filter isFree bindings

    unifyMaps ::
        InternalMap Key (TermLike RewritingVariableName) ->
        InternalMap Key (TermLike RewritingVariableName) ->
        unifier (Condition RewritingVariableName)
    unifyMaps ac1 ac2 = unifyAc (normalizeMap (builtinAcElement ac1) $ unwrapAc $ builtinAcChild ac1) (normalizeMap (builtinAcElement ac2) $ unwrapAc $ builtinAcChild ac2)

    unifySets ::
        InternalSet Key (TermLike RewritingVariableName) ->
        InternalSet Key (TermLike RewritingVariableName) ->
        unifier (Condition RewritingVariableName)
    unifySets ac1 ac2 = unifyAc (normalizeSet (builtinAcElement ac1) $ unwrapAc $ builtinAcChild ac1) (normalizeSet (builtinAcElement ac2) $ unwrapAc $ builtinAcChild ac2)

    normalizeMap ::
        Symbol ->
        NormalizedAc NormalizedMap Key (TermLike RewritingVariableName) ->
        AcCollection
    normalizeMap
        element
        NormalizedAc
            { elementsWithVariables
            , concreteElements
            , opaque
            } =
            let normalElementsWithVariables = map getMapElement elementsWithVariables
                normalConcreteElements = map normalizeConcreteMapElement $ HashMap.toList concreteElements
                variables = MultiSet.fromList $ map elemVar $ filter isVar opaque
                functions = MultiSet.fromList $ filter (not . isVar) opaque
                elements = Set.map (reconstructMapElement element) $ Set.fromList $ normalElementsWithVariables ++ normalConcreteElements
             in AcCollection{elements, variables, functions}

    reconstructMapElement element (key, val) = mkApplySymbol element [key, val]
    normalizeConcreteMapElement (key, value) = (from key, getMapValue value)

    normalizeSet ::
        Symbol ->
        NormalizedAc NormalizedSet Key (TermLike RewritingVariableName) ->
        AcCollection
    normalizeSet
        element
        NormalizedAc
            { elementsWithVariables
            , concreteElements
            , opaque
            } =
            let normalElementsWithVariables = map getSetElement elementsWithVariables
                normalConcreteElements = map normalizeConcreteSetElement $ HashMap.toList concreteElements
                variables = MultiSet.fromList $ map elemVar $ filter isVar opaque
                functions = MultiSet.fromList $ filter (not . isVar) opaque
                elements = Set.map (reconstructSetElement element) $ Set.fromList $ normalElementsWithVariables ++ normalConcreteElements
             in AcCollection{elements, variables, functions}

    reconstructSetElement element key = mkApplySymbol element [key]
    normalizeConcreteSetElement (key, _) = from key

    unifyAc ::
        AcCollection ->
        AcCollection ->
        unifier (Condition RewritingVariableName)
    unifyAc
        AcCollection{elements = elements1, variables = variables1, functions = functions1}
        AcCollection{elements = elements2, variables = variables2, functions = functions2} =
            let commonElements = Set.intersection elements1 elements2
                commonVariables = MultiSet.intersection variables1 variables2
                commonFunctions = MultiSet.intersection functions1 functions2
                uniqueElements1 = Set.difference elements1 commonElements
                uniqueElements2 = Set.difference elements2 commonElements
                uniqueVariables1 = MultiSet.difference variables1 commonVariables
                uniqueVariables2 = MultiSet.difference variables2 commonVariables
                uniqueFunctions1 = MultiSet.difference functions1 commonFunctions
                uniqueFunctions2 = MultiSet.difference functions2 commonFunctions
             in case (MultiSet.size uniqueFunctions1, MultiSet.size uniqueFunctions2) of
                    (0, 0) -> acUnify (acCollection uniqueElements1 uniqueVariables1) (acCollection uniqueElements2 uniqueVariables2)
                    _ -> constrainEquals first second

    acUnify ::
        AcCollection ->
        AcCollection ->
        unifier (Condition RewritingVariableName)
    acUnify term1@AcCollection{elements = elements1, variables = variables1} term2@AcCollection{elements = elements2, variables = variables2} =
        case (Set.size elements1, MultiSet.size variables1, Set.size elements2, MultiSet.size variables2) of
            (0, 0, 0, 0) -> discharge
            (0, 1, _, _) -> acBindVarToTerm (MultiSet.findMin variables1) $ acCollection elements2 variables2
            (_, _, 0, 1) -> acBindVarToTerm (MultiSet.findMin variables2) $ acCollection elements1 variables1
            (1, 0, 1, 0) ->
                let firstElement = Set.findMin elements1
                    secondElement = Set.findMin elements2
                 in case (firstElement, secondElement) of
                        (App_ _ firstChildren, App_ _ secondChildren) -> decomposeList (zip firstChildren secondChildren)
                        _ -> error "invalid element pattern"
            (0, 0, 0, _) -> acUnifyConcat
            (0, _, 0, 0) -> acUnifyConcat
            (0, 0, _, _) -> failUnify "Cannot unify empty collection with non-empty collection"
            (_, _, 0, 0) -> failUnify "Cannot unify empty collection with non-empty collection"
            (_, _, _, _) -> acUnifyConcat
      where
        acUnifyConcat =
            let (vars1, lhs, freeEqs1) = variableAbstraction sort vars term1
                (vars2, rhs, freeEqs2) = variableAbstraction sort vars1 term2
             in case (lhs, rhs) of
                    (AcTerm{acElements = []}, AcTerm{acElements = rhsVars, acSort}) -> acRecurse acSort (map (acBind lhs) rhsVars) vars2 (freeEqs1 ++ freeEqs2)
                    (AcTerm{acElements = lhsVars, acSort}, AcTerm{acElements = []}) -> acRecurse acSort (map (acBind rhs) lhsVars) vars2 (freeEqs1 ++ freeEqs2)
                    (AcTerm{acSort}, _) -> acRecurse acSort [Right $ AcEquation lhs rhs] vars2 (freeEqs1 ++ freeEqs2)

    acBindVarToTerm ::
        SomeVariable RewritingVariableName ->
        AcCollection ->
        unifier (Condition RewritingVariableName)
    acBindVarToTerm var collection =
        let (vars', term, freeEqs) = variableAbstraction sort vars collection
         in acRecurse sort [acBind term var] vars' freeEqs

    acBind ::
        AcTerm ->
        SomeVariable RewritingVariableName ->
        Either (SomeVariable RewritingVariableName, Binding) AcEquation
    acBind acTerm var =
        case binding var of
            Nothing -> Left (var, Ac acTerm)
            Just (Free (ElemVar_ boundVar)) -> Left (inject boundVar, Ac acTerm)
            Just (Free _) -> error "invalid free binding for AC sort"
            Just (Ac term) -> Right $ AcEquation acTerm term

    acRecurse ::
        HasCallStack =>
        Sort ->
        [Either (SomeVariable RewritingVariableName, Binding) AcEquation] ->
        Set (SomeVariableName RewritingVariableName) ->
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
        unifier (Condition RewritingVariableName)
    acRecurse acSort bindings' vars' freeEqs =
        let newBindings = union bindings $ Map.fromList $ lefts bindings'
            newAcEquations = rights bindings'
         in unifyTerms' rootSort sideCondition origVars vars' (freeEqs ++ rest) newBindings constraints $ Map.insert acSort (newAcEquations ++ Map.findWithDefault [] acSort acEquations) acEquations

    acDecompose ::
        AcTerm ->
        AcTerm ->
        unifier (Condition RewritingVariableName)
    acDecompose term1 term2 = unifyTerms' rootSort sideCondition origVars vars rest bindings constraints $ Map.insert (acSort term1) (AcEquation term1 term2 : Map.findWithDefault [] (acSort term1) acEquations) acEquations

solveAcEquations ::
    HasCallStack =>
    SmtMetadataTools Attribute.Symbol ->
    Map (SomeVariable RewritingVariableName) Binding ->
    Set (SomeVariableName RewritingVariableName) ->
    Sort ->
    [AcEquation] ->
    ([Map (SomeVariable RewritingVariableName) (TermLike RewritingVariableName)], Set (SomeVariableName RewritingVariableName))
solveAcEquations tools bindings vars sort [] =
    let acBindings = Map.filter (\acTerm -> acSort acTerm == sort) $ Map.map fromAc $ Map.filter isAc bindings
     in ([Map.map (remakeMapTerms tools) acBindings], vars)
solveAcEquations tools bindings vars sort acEquations =
    let newAcEquations = map (substituteAcVars bindings) acEquations
        p = length newAcEquations
        u = acVars newAcEquations
        n = length u
        constrainedVars = foldr unionConstrainedVars Set.empty acEquations
        constrainedIndices = IntSet.fromDistinctAscList $ map fromJust $ Set.toAscList $ Set.map (flip elemIndex $ map variableName u) constrainedVars
        system = Matrix.matrix p n (defect' newAcEquations u)
        solved = solveDiophantineEquations system
        (newVars, vars') = mkVars sort (length solved) [] vars
        basis = zip solved newVars
        suitable = allSuitableSolutions basis constrainedIndices n
        acSubst = map (makeAcSubstitution sort 0 u) suitable
        acBindings = Map.filter (\acTerm -> acSort acTerm == sort) $ Map.map fromAc $ Map.filter isAc bindings
        allAcBindings = map (union acBindings) acSubst
     in (map (Map.map (remakeMapTerms tools)) allAcBindings, vars')
  where
    defect' eqs u (i, j) = defect (eqs !! (i - 1)) (u !! (j - 1))
    unionConstrainedVars (AcEquation AcTerm{elementVars = elementVars1} AcTerm{elementVars = elementVars2}) set = Set.union set $ Set.union elementVars1 elementVars2

allSuitableSolutions ::
    [(Vector Int, ElementVariable RewritingVariableName)] ->
    IntSet ->
    Int ->
    [[(Vector Int, ElementVariable RewritingVariableName)]]
allSuitableSolutions basis constrained n =
    let m = Map.fromList basis
        (basis', _) = unzip basis
        suitable = allSuitableSolutions' basis' constrained n
     in map (\sol -> zip sol $ map (m Map.!) sol) suitable

allSuitableSolutions' ::
    [Vector Int] ->
    IntSet ->
    Int ->
    [[Vector Int]]
allSuitableSolutions' basis constrained n =
    let legal = foldl' makeLegal BDD.true [0 .. n -1]
        maximal = foldl' (makeMaximal legal) legal indexedBasis
        sat = BDD.allSatComplete (IntSet.fromDistinctAscList [0 .. length basis - 1]) maximal
     in map toSolution sat
  where
    indexedBasis = zip basis [0 .. length basis -1]
    nonNullBasis i = filter (\v -> fst v ! i /= 0) indexedBasis
    toSolution ::
        IntMap Bool ->
        [Vector Int]
    toSolution intmap =
        map fst $ filter ((intmap IntMap.!) . snd) indexedBasis
    makeLower :: Int -> BDD AscOrder -> BDD AscOrder
    makeLower i bdd =
        bdd .&&. BDD.orB (map (BDD.var . snd) $ nonNullBasis i)
    makeUpper :: Int -> BDD AscOrder -> BDD AscOrder
    makeUpper i bdd = bdd .&&. snd (foldl' (makeBounds i) (BDD.true, BDD.true) $ nonNullBasis i)
    makeBounds i (bounds0, bounds1) v =
        let value = fst v ! i
            bounds1' = if value <= 1 then BDD.ite (BDD.var $ snd v) bounds0 bounds1 else BDD.ite (BDD.var $ snd v) BDD.false bounds1
            bounds0' = BDD.ite (BDD.var $ snd v) BDD.false bounds0
         in (bounds0', bounds1')
    makeLegal ::
        BDD AscOrder ->
        Int ->
        BDD AscOrder
    makeLegal bdd i =
        if IntSet.member i constrained
            then makeLower i $ makeUpper i bdd
            else bdd
    makeMaximal ::
        BDD AscOrder ->
        BDD AscOrder ->
        (Vector Int, Int) ->
        BDD AscOrder
    makeMaximal legal maximal (_, i) =
        maximal .&&. (BDD.var i .||. BDD.notB (BDD.restrict i True legal))

substituteAcVars ::
    Map (SomeVariable RewritingVariableName) Binding ->
    AcEquation ->
    AcEquation
substituteAcVars bindings (AcEquation term1 term2) =
    AcEquation (substituteAc term1) (substituteAc term2)
  where
    substituteAc term@AcTerm{acElements = elements} =
        term{acElements = substitute' elements}
    substitute' [] = []
    substitute' (x : xs) | Just (Ac AcTerm{acElements = xs'}) <- Map.lookup x bindings = xs' ++ xs
    substitute' (x : xs) = x : substitute' xs

remakeMapTerms ::
    SmtMetadataTools Attribute.Symbol ->
    AcTerm ->
    TermLike RewritingVariableName
remakeMapTerms _ AcTerm{acElements = [var]} =
    mkElemVar $ fromJust $ retract var
remakeMapTerms tools AcTerm{acElements, acSort} =
    if fromJust $ isMapSort tools acSort
        then Ac.asInternal tools acSort $ NormalizedMap{getNormalizedMap = normalizedAc $ map mkVar acElements}
        else Ac.asInternal tools acSort $ NormalizedSet{getNormalizedSet = normalizedAc $ map mkVar acElements}
  where
    normalizedAc opaque = NormalizedAc{elementsWithVariables = [], concreteElements = HashMap.empty, opaque}

acVars ::
    [AcEquation] ->
    [SomeVariable RewritingVariableName]
acVars [] = []
acVars eqs = go eqs Set.empty
  where
    go [] set = Set.toList set
    go (AcEquation term1 term2 : eqs') set =
        go eqs' $ collectAcVars term1 $ collectAcVars term2 set
    collectAcVars AcTerm{acElements} set =
        Set.union set (Set.fromList acElements)

defect ::
    AcEquation ->
    SomeVariable RewritingVariableName ->
    Int
defect (AcEquation term1 term2) var =
    count var (acElements term1) - count var (acElements term2)
  where
    count :: Eq a => a -> [a] -> Int
    count x = length . filter (x ==)

solveDiophantineEquations ::
    Matrix Int ->
    [Vector Int]
solveDiophantineEquations system =
    let vk = v1 m
     in Set.toList $ computeStep vk (makeMk vk)
  where
    m = Matrix.ncols system
    n = Matrix.nrows system
    v1 :: Int -> Set (Vector Int)
    v1 0 = Set.empty
    v1 i = Set.insert (e i) $ v1 (i -1)
    e :: Int -> Vector Int
    e i = Vector.generate m (\j -> if j + 1 == i then 1 else 0)
    makeMk :: Set (Vector Int) -> Set (Vector Int)
    makeMk vk = Set.filter (\v -> defect' v == Vector.replicate n 0) vk
    defect' :: Vector Int -> Vector Int
    defect' v = Matrix.getCol 1 $ Matrix.multStd system $ Matrix.colVector v

    computeStep :: Set (Vector Int) -> Set (Vector Int) -> Set (Vector Int)
    computeStep vk mk | Set.null vk = mk
    computeStep vk mk =
        let newVk = vk' vk mk
         in computeStep newVk $ Set.union mk $ makeMk newVk

    vk' :: Set (Vector Int) -> Set (Vector Int) -> Set (Vector Int)
    vk' vk mk =
        Set.fromList [add v (e j) | v <- Set.toList $ Set.difference vk mk, j <- [0 .. m -1], isMinimal v (e j) mk, dot (defect' v) (defect' (e j)) < 0]

    isMinimal :: Vector Int -> Vector Int -> Set (Vector Int) -> Bool
    isMinimal v ej mk = all (not . gt (add v ej)) mk

    gt :: Vector Int -> Vector Int -> Bool
    gt a b =
        let zipped = Vector.zipWith (,) a b
         in all (uncurry (>=)) zipped && any (uncurry (>)) zipped

    add :: Vector Int -> Vector Int -> Vector Int
    add a b = Vector.zipWith (+) a b

    dot :: Vector Int -> Vector Int -> Int
    dot a b = Vector.sum $ Vector.zipWith (*) a b

makeAcSubstitution ::
    Sort ->
    Int ->
    [SomeVariable RewritingVariableName] ->
    [(Vector Int, ElementVariable RewritingVariableName)] ->
    Map (SomeVariable RewritingVariableName) AcTerm
makeAcSubstitution _ _ [] _ = Map.empty
makeAcSubstitution sort i (ui : u) basis =
    let acTerm = makeAcSubstitutionTerm sort basis i
     in Map.insert ui acTerm $ makeAcSubstitution sort (i + 1) u basis

makeAcSubstitutionTerm ::
    Sort ->
    [(Vector Int, ElementVariable RewritingVariableName)] ->
    Int ->
    AcTerm
makeAcSubstitutionTerm acSort basis i =
    AcTerm{acElements = concatMap (makeAcSubstitutionSubterm i) basis, acSort, elementVars = Set.empty}

makeAcSubstitutionSubterm ::
    Int ->
    (Vector Int, ElementVariable RewritingVariableName) ->
    [SomeVariable RewritingVariableName]
makeAcSubstitutionSubterm i (sk, vk) =
    replicate (sk ! i) $ inject vk

acCollection ::
    Set (TermLike RewritingVariableName) ->
    MultiSet (SomeVariable RewritingVariableName) ->
    AcCollection
acCollection elements variables = AcCollection{elements, variables, functions = MultiSet.empty}

mkVars ::
    Sort ->
    Int ->
    [ElementVariable RewritingVariableName] ->
    Set (SomeVariableName RewritingVariableName) ->
    ([ElementVariable RewritingVariableName], Set (SomeVariableName RewritingVariableName))
mkVars _ 0 accum vars = (accum, vars)
mkVars sort n accum vars =
    let varName = ElementVariableName $ mkConfigVariable $ mkVariableName $ generatedId (Text.concat ["VarAC", Text.pack $ show n, "'Unds'"])
        newVar = Variable{variableName = varName, variableSort = sort}
        renamedVar = refreshVariable vars (inject newVar)
        finalVar = maybe newVar (fromJust . retract) renamedVar
     in mkVars sort (n -1) (finalVar : accum) $ Set.insert (variableName $ inject finalVar) vars

variableAbstraction ::
    Sort ->
    Set (SomeVariableName RewritingVariableName) ->
    AcCollection ->
    (Set (SomeVariableName RewritingVariableName), AcTerm, [(TermLike RewritingVariableName, TermLike RewritingVariableName)])
variableAbstraction acSort vars AcCollection{elements, variables} =
    let elementsList = Set.toList elements
        (newVars, renamedVars) = mkVars acSort (length elementsList) [] vars
        newTerms = map mkElemVar newVars
        acElements = (map inject newVars) ++ MultiSet.toList variables
        term = AcTerm{acElements, acSort, elementVars = Set.difference renamedVars vars}
     in (renamedVars, term, zip newTerms elementsList)
