{- |
Module      : Kore.Builtin.Set
Description : Built-in sets
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Set as Set
@
 -}
module Kore.Builtin.Set
    ( sort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    , Builtin
    , asPattern
    , asExpandedPattern
      -- * Symbols
    , lookupSymbolUnit
    , lookupSymbolElement
    , lookupSymbolConcat
    , lookupSymbolIn
    , lookupSymbolDifference
      -- * Unification
    , unify
    ) where

import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import qualified Control.Monad.Except as Except
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
import qualified Kore.AST.PureML as Kore
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier, Simplifier, SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh
                 ( FreshVariable )
import           Data.Result
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.ASTUtils.SmartPatterns
import           Control.Monad.Counter
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions, normalizePredicatedSubstitution )
import           Data.Reflection ( give )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Control.Applicative
                 ( Alternative (..) )

{- | Builtin name of the @Set@ sort.
 -}
sort :: String
sort = "SET.Set"

{- | Verify that the sort is hooked to the builtin @Set@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort findSort = Builtin.verifySort findSort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( "SET.concat"
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( "SET.element"
      , Builtin.verifySymbol assertSort [anySort]
      )
    , ( "SET.unit"
      , Builtin.verifySymbol assertSort []
      )
    , ( "SET.in"
      , Builtin.verifySymbol Bool.assertSort [anySort, assertSort]
      )
    , ( "SET.difference"
      , Builtin.verifySymbol assertSort [assertSort, assertSort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

type Builtin = Set (Kore.ConcretePurePattern Object)

{- | Abort function evaluation if the argument is not a @Set@ domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented by a
    'BuiltinDomainSet', it is a bug.

 -}
expectBuiltinDomainSet
    :: Monad m
    => String  -- ^ Context for error message
    -> MetadataTools Object StepperAttributes
    -> Kore.PureMLPattern Object variable  -- ^ Operand pattern
    -> ExceptT (AttemptedFunction Object variable) m Builtin
expectBuiltinDomainSet ctx tools _set =
    do
        _set <- Builtin.expectNormalConcreteTerm tools _set
        case _set of
            Kore.DV_ _ domain ->
                case domain of
                    Kore.BuiltinDomainSet set -> return set
                    _ ->
                        Builtin.verifierBug
                            (ctx ++ ": Domain value is not a set")
            _ ->
                Except.throwError NotApplicable

returnSet
    :: Monad m
    => Kore.Sort Object
    -> Builtin
    -> m (AttemptedFunction Object variable)
returnSet resultSort set =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ Kore.DV_ resultSort
        $ Kore.BuiltinDomainSet set

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (case arguments of
            [_elem] -> do
                _elem <- Builtin.expectNormalConcreteTerm tools _elem
                returnSet resultSort (Set.singleton _elem)
            _ -> Builtin.wrongArity "SET.element"
        )

evalIn :: Builtin.Function
evalIn =
    Builtin.functionEvaluator evalIn0
  where
    evalIn0
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object variable
        -> Kore.Sort Object
        -> [Kore.PureMLPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalIn0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_elem, _set) =
                    case arguments of
                        [_elem, _set] -> (_elem, _set)
                        _ -> Builtin.wrongArity "SET.in"
            _elem <- Builtin.expectNormalConcreteTerm tools _elem
            _set <- expectBuiltinDomainSet "SET.in" tools _set
            (Builtin.appliedFunction . asExpandedBoolPattern)
                (Set.member _elem _set)
        )
      where
        asExpandedBoolPattern = Bool.asExpandedPattern resultSort

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ _ resultSort =
        \case
            [] -> returnSet resultSort Set.empty
            _ -> Builtin.wrongArity "SET.unit"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    ctx = "SET.concat"
    evalConcat0
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object variable
        -> Kore.Sort Object
        -> [Kore.PureMLPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalConcat0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity ctx
            _set1 <- expectBuiltinDomainSet ctx tools _set1
            _set2 <- expectBuiltinDomainSet ctx tools _set2
            returnSet resultSort (_set1 <> _set2)
        )

evalDifference :: Builtin.Function
evalDifference =
    Builtin.functionEvaluator evalDifference0
  where
    ctx = "SET.difference"
    evalDifference0
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object variable
        -> Kore.Sort Object
        -> [Kore.PureMLPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalDifference0 tools _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity ctx
            _set1 <- expectBuiltinDomainSet ctx tools _set1
            _set2 <- expectBuiltinDomainSet ctx tools _set2
            returnSet resultSort (Set.difference _set1 _set2)
        )

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
        [ ("SET.concat", evalConcat)
        , ("SET.element", evalElement)
        , ("SET.unit", evalUnit)
        , ("SET.in", evalIn)
        , ("SET.difference", evalDifference)
        ]

{- | Render a 'Set' as a domain value pattern of the given sort.

    The result sort should be hooked to the builtin @Set@ sort, but this is not
    checked.

    The constructed pattern will be valid in the contexed of the given indexed
    module. It is an error if the indexed module does not define symbols hooked
    to @SET.unit@, @SET.element@, and @SET.concat@.

    See also: 'sort'

 -}
asPattern
    :: KoreIndexedModule attrs
    -- ^ indexed module where pattern would appear
    -> Kore.Sort Object
    -> Either
        (Kore.Error e)
        (Builtin -> Kore.PureMLPattern Object variable)
asPattern indexedModule _ = do
    symbolUnit <- lookupSymbolUnit indexedModule
    let
        applyUnit :: Kore.PureMLPattern Object variable
        applyUnit = Kore.App_ symbolUnit []
    symbolElement <- lookupSymbolElement indexedModule
    let
        applyElement
            :: Kore.ConcretePurePattern Object
            -> Kore.PureMLPattern Object variable
        applyElement elem' =
            Kore.App_ symbolElement [Kore.fromConcretePurePattern elem']
    symbolConcat <- lookupSymbolConcat indexedModule
    let
        applyConcat
            :: Kore.PureMLPattern Object variable
            -> Kore.PureMLPattern Object variable
            -> Kore.PureMLPattern Object variable
        applyConcat set1 set2 = Kore.App_ symbolConcat [set1, set2]
    let
        asPattern0
            :: Builtin -> Kore.PureMLPattern Object variable
        asPattern0 set =
            foldr applyConcat applyUnit
                (applyElement <$> Foldable.toList set)
    return asPattern0

{- | Render a 'Seq' as an extended domain value pattern.

    See also: 'asPattern'

 -}
asExpandedPattern
    :: KoreIndexedModule attrs
    -- ^ dictionary of Map constructor symbols
    -> Kore.Sort Object
    -> Either
        (Kore.Error e)
        (Builtin -> ExpandedPattern Object variable)
asExpandedPattern symbols resultSort =
    asExpandedPattern0 <$> asPattern symbols resultSort
  where
    asExpandedPattern0 = \asPattern0 builtin ->
        ExpandedPattern.fromPurePattern $ asPattern0 builtin

{- | Find the symbol hooked to @SET.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "SET.unit"

{- | Find the symbol hooked to @SET.element@ in an indexed module.
 -}
lookupSymbolElement
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "SET.element"

{- | Find the symbol hooked to @SET.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "SET.concat"

{- | Find the symbol hooked to @SET.get@ in an indexed module.
 -}
lookupSymbolIn
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolIn = Builtin.lookupSymbol "SET.in"

{- | Find the symbol hooked to @SET.difference@ in an indexed module.
 -}
lookupSymbolDifference
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolDifference = Builtin.lookupSymbol "SET.difference"

{- | Simplify the conjunction of two concrete Set domain values.

    The sets are assumed to have the same sort, but this is not checked. If
    multiple sorts are hooked to the same builtin domain, the verifier should
    reject the definition.
 -}

unify
    :: forall level variable m p expanded proof.
        ( OrdMetaOrObject variable, ShowMetaOrObject variable
        , Kore.SortedVariable variable
        , MonadCounter m
        , MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , p ~ Kore.PureMLPattern level variable
        , expanded ~ ExpandedPattern level variable
        , proof ~ SimplificationProof level
        )
    => MetadataTools level StepperAttributes
    -> (p -> p -> Result (m (expanded, proof)))
    -> (p -> p -> Result (m (expanded, proof)))
unify
    tools@(MetadataTools.MetadataTools { symbolOrAliasSorts })
    simplifyChild
  = 
    unify0
  where
    -- | Normalize the substitution of 'expanded', or return 'bottom' if
    -- normalization fails.
    -- NB: this is exactly the same for maps. Move and share?
    normalize :: (level ~ Object) => expanded -> m expanded
    normalize r =
        runExceptT (normalizePredicatedSubstitution tools r)
            >>= \case
                Left _ -> return ExpandedPattern.bottom
                Right (normalized, _) -> return normalized

    -- | Unify the two argument patterns.
    unify0
        :: Kore.PureMLPattern level variable
        -> Kore.PureMLPattern level variable
        -> Result (m (expanded, proof))
    unify0 
        (DV_ sort (Kore.BuiltinDomainSet set1))
        (DV_ _    (Kore.BuiltinDomainSet set2))
      = 
        unifyConcrete sort set1 set2

    unify0 
        (App_ _ [DV_ _ (Kore.BuiltinDomainSet set1), x@(Var_ _)])
        second@(DV_ sort (Kore.BuiltinDomainSet set2))
      = 
        unifyFramed sort set1 set2 x
 
    unify0 app_@(App_ _ _) dv_@(DV_ _ _) = unify0 dv_ app_
    
    unify0 _ _ = empty
    
    -- | Unify two concrete sets
    unifyConcrete
        :: (level ~ Object, k ~ Kore.ConcretePurePattern Object)
        => Kore.Sort level -- ^ Sort of result
        -> Set.Set k
        -> Set.Set k
        -> Result (m (expanded, proof))
    unifyConcrete resultSort set1 set2 = do -- Result monad
        let 
            term = DV_ resultSort (Kore.BuiltinDomainSet set1)
            unified = give symbolOrAliasSorts $ do -- MonadCounter 
                let 
                    result 
                        | set1 == set2 = pure term
                        | otherwise    = ExpandedPattern.bottom
                (,) <$> normalize result <*> pure SimplificationProof
        return unified

    -- | Unify one concrete set with one framed concrete set.
    unifyFramed
        :: (level ~ Object, k ~ Kore.ConcretePurePattern Object)
        => Kore.Sort level  -- ^ Sort of result
        -> Set.Set k  -- ^ concrete set
        -> Set.Set k -- ^ framed concrete set
        -> Kore.PureMLPattern level variable  -- ^ framing variable
        -> Result (m (expanded, proof))
    unifyFramed resultSort set1 set2 (Var_ x) = do -- Result monad
        let 
            term' = DV_ resultSort (Kore.BuiltinDomainSet set2)
            diff = Set.difference set2 set1
            unified = do -- MonadCounter
                let
                    result 
                        | Set.isSubsetOf set1 set2 = 
                            Predicated
                            { term = term'
                            , predicate = makeTruePredicate
                            , substitution = [(x, DV_ resultSort (Kore.BuiltinDomainSet diff))]
                            }
                        | otherwise = ExpandedPattern.bottom
                (,) <$> normalize result <*> pure SimplificationProof
        return unified