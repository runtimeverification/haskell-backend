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
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import           Data.Sequence
                 ( Seq )
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
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
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
    :: (Monad m, Ord (variable Object))
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
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
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
                    (Builtin.appliedFunction . maybeBottom)
                        (Seq.lookup ix _list)
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
        :: Ord (variable Object)
        => MetadataTools Object StepperAttributes
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
    -> Either (Kore.Error e)
        (Builtin variable -> Kore.PureMLPattern Object variable)
asPattern indexedModule dvSort = do
    symbolUnit <- lookupSymbolUnit dvSort indexedModule
    let applyUnit = Kore.App_ symbolUnit []
    symbolElement <- lookupSymbolElement dvSort indexedModule
    let applyElement elem' = Kore.App_ symbolElement [elem']
    symbolConcat <- lookupSymbolConcat dvSort indexedModule
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
    -> Either (Kore.Error e)
        (Builtin variable -> ExpandedPattern Object variable)
asExpandedPattern symbols resultSort =
    (ExpandedPattern.fromPurePattern .) <$> asPattern symbols resultSort

{- | Find the symbol hooked to @LIST.unit@ in an indexed module.
 -}
lookupSymbolUnit
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolUnit = Builtin.lookupSymbol "LIST.unit"

{- | Find the symbol hooked to @LIST.element@ in an indexed module.
 -}
lookupSymbolElement
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolElement = Builtin.lookupSymbol "LIST.element"

{- | Find the symbol hooked to @LIST.concat@ in an indexed module.
 -}
lookupSymbolConcat
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolConcat = Builtin.lookupSymbol "LIST.concat"

{- | Find the symbol hooked to @LIST.get@ in an indexed module.
 -}
lookupSymbolGet
    :: Sort Object
    -> KoreIndexedModule attrs
    -> Either (Kore.Error e) (Kore.SymbolOrAlias Object)
lookupSymbolGet = Builtin.lookupSymbol "LIST.get"

isSymbolConcat
    :: MetadataTools Object Hook
    -> Kore.SymbolOrAlias Object
    -> Bool
isSymbolConcat = Builtin.isSymbol "LIST.concat"

isSymbolElement
    :: MetadataTools Object Hook
    -> Kore.SymbolOrAlias Object
    -> Bool
isSymbolElement = Builtin.isSymbol "LIST.element"

unify
    :: forall level variable m p expanded proof.
        ( OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Ord (variable level)
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
    -> (p -> p -> m (expanded, proof))
    -> (p -> p -> MaybeT m (expanded, proof))
unify
    tools@MetadataTools { symbolOrAliasSorts }
    _
    simplifyChild
  =
    unify0
  where
    hookTools = StepperAttributes.hook <$> tools

    propagatePredicates
        :: Traversable t
        => t (Predicated level variable a)
        -> Predicated level variable (t a)
    propagatePredicates = give symbolOrAliasSorts sequenceA

    discardProofs :: Seq (expanded, proof) -> Seq expanded
    discardProofs = (<$>) fst

    unify0
        :: PureMLPattern level variable
        -> PureMLPattern level variable
        -> MaybeT m (expanded, proof)

    unify0 dv1@(DV_ resultSort (BuiltinDomainList list1)) =
        \case
            dv2@(DV_ _ builtin2) ->
                case builtin2 of
                    BuiltinDomainList list2 ->
                        Monad.Trans.lift $ unifyConcrete resultSort list1 list2
                    _ ->
                        (error . unlines)
                            [ "Cannot unify a builtin List domain value:"
                            , show dv1
                            , "with:"
                            , show dv2
                            , "This should have been a sort error."
                            ]
            app@(App_ symbol2 args2)
              | isSymbolConcat hookTools symbol2 ->
                Monad.Trans.lift $ case args2 of
                    [ DV_ _ (BuiltinDomainList list2), x@(Var_ _) ] ->
                        unifyFramedRight resultSort list1 symbol2 list2 x
                    [ x@(Var_ _), DV_ _ (BuiltinDomainList list2) ] ->
                        unifyFramedLeft resultSort list1 symbol2 x list2
                    [ _, _ ] ->
                        give symbolOrAliasSorts Builtin.unifyUnsolved dv1 app
                    _ -> Builtin.wrongArity "LIST.concat"
              | otherwise -> empty
            _ -> empty

    unify0 pat1 =
        \case
            dv@(DV_ _ (BuiltinDomainList _)) -> unify0 dv pat1
            _ -> empty

    unifyConcrete
        :: (level ~ Object)
        => Sort level
        -> Seq p
        -> Seq p
        -> m (expanded, proof)
    unifyConcrete dvSort list1 list2
      | Seq.length list1 /= Seq.length list2 =
        return (ExpandedPattern.bottom, SimplificationProof)
      | otherwise =
        do
            unified <-
                sequence $ Seq.zipWith simplifyChild list1 list2
            let
                propagatedUnified =
                    (propagatePredicates . discardProofs) unified
                result = asBuiltinDomainList <$> propagatedUnified
            return (result, SimplificationProof)
      where
        asBuiltinDomainList = DV_ dvSort . BuiltinDomainList

    unifyFramedRight
        :: (level ~ Object)
        => Sort level
        -> Seq p
        -> SymbolOrAlias level
        -> Seq p
        -> p
        -> m (expanded, proof)
    unifyFramedRight resultSort list1 symConcat prefix2 frame2
      | Seq.length prefix2 > Seq.length list1 =
        return (ExpandedPattern.bottom, SimplificationProof)
      | otherwise =
        do
            (prefixUnified, _) <- unifyConcrete resultSort prefix1 prefix2
            (suffixUnified, _) <- simplifyChild frame2 listSuffix1
            let result =
                    (<$>)
                        (App_ symConcat)
                        (propagatePredicates [prefixUnified, suffixUnified])
            return (result, SimplificationProof)
      where
        asBuiltinDomainList = DV_ resultSort . BuiltinDomainList
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length prefix2
        listSuffix1 = asBuiltinDomainList suffix1

    unifyFramedLeft
        :: level ~ Object
        => Sort level
        -> Seq p
        -> SymbolOrAlias level
        -> p
        -> Seq p
        -> m (expanded, proof)
    unifyFramedLeft resultSort list1 symConcat frame2 suffix2
      | Seq.length suffix2 > Seq.length list1 =
        return (ExpandedPattern.bottom, SimplificationProof)
      | otherwise =
        do
            (prefixUnified, _) <- simplifyChild frame2 listPrefix1
            (suffixUnified, _) <- unifyConcrete resultSort suffix1 suffix2
            let result =
                    (<$>)
                        (App_ symConcat)
                        (propagatePredicates [prefixUnified, suffixUnified])
            return (result, SimplificationProof)
      where
        asBuiltinDomainList = DV_ resultSort . BuiltinDomainList
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length list1 - Seq.length suffix2
        listPrefix1 = asBuiltinDomainList prefix1
