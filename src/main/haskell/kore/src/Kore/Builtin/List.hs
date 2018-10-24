{- |
Module      : Kore.Builtin.List
Description : Built-in associative lists
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.List as List
@
 -}
module Kore.Builtin.List
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
    , lookupSymbolGet
    , isSymbolConcat
    , isSymbolElement
    , unify
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import           Data.Result
import           Data.Sequence
                 ( Seq, (><) )
import qualified Data.Sequence as Seq
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( Hook )
import qualified Kore.Builtin.Int as Int
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
import           Kore.Step.Substitution
                 ( normalize )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

{- | Builtin variable name of the @List@ sort.
 -}
sort :: Text
sort = "LIST.List"

{- | Verify that the sort is hooked to the builtin @List@ sort.

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
    [ ( "LIST.concat"
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( "LIST.element"
      , Builtin.verifySymbol assertSort [anySort]
      )
    , ( "LIST.unit"
      , Builtin.verifySymbol assertSort []
      )
    , ( "LIST.get"
      , Builtin.verifySymbol anySort [assertSort, Int.assertSort]
      )
    ]
  where
    anySort :: Builtin.SortVerifier
    anySort = const $ const $ Right ()

type Builtin variable = Seq (Kore.PureMLPattern Object variable)

{- | Abort function evaluation if the argument is not a List domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainList', it is a bug.

 -}
expectBuiltinDomainList
    :: Monad m
    => String  -- ^ Context for error message
    -> Kore.PureMLPattern Object variable  -- ^ Operand pattern
    -> MaybeT m (Builtin variable)
expectBuiltinDomainList ctx =
    \case
        Kore.DV_ _ domain ->
            case domain of
                Kore.BuiltinDomainList list -> return list
                _ -> Builtin.verifierBug (ctx ++ ": Domain value is not a list")
        _ ->
            empty

returnList
    :: Monad m
    => Kore.Sort Object
    -> (Builtin variable)
    -> m (AttemptedFunction Object variable)
returnList resultSort list =
    Builtin.appliedFunction
        $ ExpandedPattern.fromPurePattern
        $ Kore.DV_ resultSort
        $ Kore.BuiltinDomainList list

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ _ resultSort = \arguments ->
        case arguments of
            [elem'] -> returnList resultSort (Seq.singleton elem')
            _ -> Builtin.wrongArity "LIST.element"

evalGet :: Builtin.Function
evalGet =
    Builtin.functionEvaluator evalGet0
  where
    ctx = "LIST.get"
    evalGet0
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object variable
        -> Kore.Sort Object
        -> [Kore.PureMLPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalGet0 _ _ _ = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_list, _ix) =
                    case arguments of
                        [_list, _ix] -> (_list, _ix)
                        _ -> Builtin.wrongArity ctx
                emptyList = do
                    _list <- expectBuiltinDomainList ctx _list
                    if Seq.null _list
                        then Builtin.appliedFunction ExpandedPattern.bottom
                        else empty
                bothConcrete = do
                    _list <- expectBuiltinDomainList ctx _list
                    _ix <- fromInteger <$> Int.expectBuiltinDomainInt ctx _ix
                    let ix
                            | _ix < 0 =
                                -- negative indices count from end of list
                                _ix + Seq.length _list
                            | otherwise = _ix
                    (Builtin.appliedFunction . maybeBottom) (Seq.lookup ix _list)
            emptyList <|> bothConcrete
        )
    maybeBottom =
        maybe ExpandedPattern.bottom ExpandedPattern.fromPurePattern

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ _ resultSort =
        \case
            [] -> returnList resultSort Seq.empty
            _ -> Builtin.wrongArity "LIST.unit"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    ctx = "LIST.concat"
    evalConcat0
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object variable
        -> Kore.Sort Object
        -> [Kore.PureMLPattern Object variable]
        -> Simplifier (AttemptedFunction Object variable)
    evalConcat0 _ _ resultSort = \arguments ->
        Builtin.getAttemptedFunction
        (do
            let (_list1, _list2) =
                    case arguments of
                        [_list1, _list2] -> (_list1, _list2)
                        _ -> Builtin.wrongArity ctx
                leftIdentity = do
                    _list1 <- expectBuiltinDomainList ctx _list1
                    if Seq.null _list1
                        then
                            Builtin.appliedFunction
                            $ ExpandedPattern.fromPurePattern _list2
                        else
                            empty
                rightIdentity = do
                    _list2 <- expectBuiltinDomainList ctx _list2
                    if Seq.null _list2
                        then
                            Builtin.appliedFunction
                            $ ExpandedPattern.fromPurePattern _list1
                        else
                            empty
                bothConcrete = do
                    _list1 <- expectBuiltinDomainList ctx _list1
                    _list2 <- expectBuiltinDomainList ctx _list2
                    returnList resultSort (_list1 <> _list2)
            leftIdentity <|> rightIdentity <|> bothConcrete
        )

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ ("LIST.concat", evalConcat)
        , ("LIST.element", evalElement)
        , ("LIST.unit", evalUnit)
        , ("LIST.get", evalGet)
        ]

{- | Render a 'Seq' as a domain value pattern of the given sort.

    The result sort should be hooked to the builtin @List@ sort, but this is not
    checked.

    The constructed pattern will be valid in the contexed of the given indexed
    module. It is an error if the indexed module does not define symbols hooked
    to @LIST.unit@, @LIST.element@, and @LIST.concat@.

    See also: 'sort'

 -}
asPattern
    :: KoreIndexedModule attrs
    -- ^ indexed module where pattern would appear
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin variable -> Kore.PureMLPattern Object variable)
asPattern indexedModule _ = do
    symbolUnit <- lookupSymbolUnit indexedModule
    let applyUnit = Kore.App_ symbolUnit []
    symbolElement <- lookupSymbolElement indexedModule
    let applyElement elem' = Kore.App_ symbolElement [elem']
    symbolConcat <- lookupSymbolConcat indexedModule
    let applyConcat list1 list2 = Kore.App_ symbolConcat [list1, list2]
    let asPattern0 list =
            foldr applyConcat applyUnit
            $ Foldable.toList (applyElement <$> list)
    return asPattern0

{- | Render a 'Seq' as an extended domain value pattern.

    See also: 'asPattern'

 -}
asExpandedPattern
    :: KoreIndexedModule attrs
    -- ^ dictionary of Map constructor symbols
    -> Kore.Sort Object
    -> Either (Kore.Error e) (Builtin variable -> ExpandedPattern Object variable)
asExpandedPattern symbols resultSort =
    (ExpandedPattern.fromPurePattern .) <$> asPattern symbols resultSort

{- | Find the symbol hooked to @LIST.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "LIST.unit"

{- | Find the symbol hooked to @LIST.element@ in an indexed module.
 -}
lookupSymbolElement
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "LIST.element"

{- | Find the symbol hooked to @LIST.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "LIST.concat"

{- | Find the symbol hooked to @LIST.get@ in an indexed module.
 -}
lookupSymbolGet
    :: KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolGet = Builtin.lookupSymbol "LIST.get"

isSymbolConcat :: MetadataTools Object Hook -> Kore.SymbolOrAlias Object -> Bool
isSymbolConcat = Builtin.isSymbol "LIST.concat"

isSymbolElement :: MetadataTools Object Hook -> Kore.SymbolOrAlias Object -> Bool
isSymbolElement = Builtin.isSymbol "LIST.element"

unify
    :: forall level variable m p expanded proof.
        ( OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Show (variable level)
        , SortedVariable variable
        , MonadCounter m
        , MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , p ~ PureMLPattern level variable
        , expanded ~ ExpandedPattern level variable
        , proof ~ SimplificationProof level
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> (p -> p -> Result (m (expanded, proof)))
    -> (p -> p -> Result (m (expanded, proof)))
unify
    tools@MetadataTools { symbolOrAliasSorts }
    substitutionSimplifier
    simplifyChild
    (DV_ dvSort (BuiltinDomainList list1))
    (DV_ _    (BuiltinDomainList list2))
  | Seq.length list1 /= Seq.length list2 = Failure
  | otherwise = give symbolOrAliasSorts $ do
      unifiedList <- sequence $ Seq.zipWith simplifyChild list1 list2
      return $ do
        unifiedList' <-
          sequenceA -- float `Predicated` to the top
          <$> fmap fst -- discard the proof in (expanded, proof)
          <$> sequence unifiedList -- float the counter monad `m` to the top
        res <- normalize tools substitutionSimplifier $
          (\l -> DV_ dvSort $ BuiltinDomainList l) <$> unifiedList'
        return (res, SimplificationProof)
unify
    tools@MetadataTools { symbolOrAliasSorts }
    substitutionSimplifier
    simplifyChild
    (App_ symConcat [DV_ _ (BuiltinDomainList list1), (Var_ v)])
    (DV_ dvSort (BuiltinDomainList list2))
  | Seq.length list1 > Seq.length list2 = Failure
  | isSymbolConcat (StepperAttributes.hook <$> tools) symConcat
  = give symbolOrAliasSorts $
    let list2' = Seq.take (Seq.length list1) list2
        suffix = Seq.drop (Seq.length list1) list2
        suffix' = Predicated
            { term = suffix
            , predicate = makeTruePredicate
            , substitution = [(v, DV_ dvSort $ BuiltinDomainList suffix)]
            }

      in
      do unifiedList <-
            unify tools substitutionSimplifier simplifyChild
                (DV_ dvSort $ BuiltinDomainList list1)
                (DV_ dvSort $ BuiltinDomainList list2')
         return $ do
            (unifiedList', _) <- unifiedList
            res <- normalize tools substitutionSimplifier $
                (\(DV_ _ (BuiltinDomainList l1)) l2
                    -> DV_ dvSort (BuiltinDomainList $ l1 >< l2)
                ) <$> unifiedList' <*> suffix'
            return (res, SimplificationProof)
unify
    tools
    substitutionSimplifier
    simplifyChild
    p1@(DV_ _ _)
    p2@(App_ _ _)
  = unify tools substitutionSimplifier simplifyChild p2 p1
unify _ _ _ _ _ = Unknown
