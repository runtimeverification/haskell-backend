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
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , builtinFunctions
    , Builtin
    , returnList
    , asPattern
    , asInternal
    , asTermLike
    , internalize
      -- * Symbols
    , lookupSymbolGet
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , unifyEquals
      -- * keys
    , concatKey
    , elementKey
    , unitKey
    , getKey
    , expectConcreteBuiltinList
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Control.Monad
                 ( join )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Control.Monad.Trans.Maybe as Monad.Trans.Maybe
                 ( mapMaybeT )
import qualified Data.Function as Function
import           Data.Functor
                 ( (<$) )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Reflection as Reflection
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Builtin.Builtin
                 ( acceptAnySort )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.Syntax.Sentence
                 ( SentenceSort (..) )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh

{- | Builtin variable name of the @List@ sort.
 -}
sort :: Text
sort = "LIST.List"

{- | Verify that the sort is hooked to the builtin @List@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers =
    HashMap.fromList [ (sort, verifySortDecl) ]
  where
    verifySortDecl indexedModule sentenceSort attrs = do
        Builtin.verifySortDecl indexedModule sentenceSort attrs
        unitId <- Builtin.getUnitId attrs
        Builtin.assertSymbolHook indexedModule unitId unitKey
        Builtin.assertSymbolResultSort indexedModule unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook indexedModule elementId elementKey
        Builtin.assertSymbolResultSort indexedModule elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook indexedModule concatId concatKey
        Builtin.assertSymbolResultSort indexedModule concatId expectedSort
        return ()
      where
        SentenceSort { sentenceSortName } = sentenceSort
        expectedSort = mkSort sentenceSortName

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( concatKey
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( elementKey
      , Builtin.verifySymbol assertSort [acceptAnySort]
      )
    , ( unitKey
      , Builtin.verifySymbol assertSort []
      )
    , ( getKey
      , Builtin.verifySymbol acceptAnySort [assertSort, Int.assertSort]
      )
    ]

{- | Abort function evaluation if the argument is not a List domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainList', it is a bug.

 -}
expectBuiltinList
    :: Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Seq (TermLike variable))
expectBuiltinList ctx =
    \case
        Builtin_ domain ->
            case domain of
                Domain.BuiltinList Domain.InternalList { builtinListChild } ->
                    return builtinListChild
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a list"
        _ -> empty

expectConcreteBuiltinList
    :: Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Seq (TermLike Concrete))
expectConcreteBuiltinList ctx =
    Monad.Trans.Maybe.mapMaybeT (fmap join)
        . fmap (traverse Builtin.toKey)
        . expectBuiltinList ctx

returnList
    :: (MonadSimplify m, Ord variable, SortedVariable variable)
    => Sort
    -> Seq (TermLike variable)
    -> m (AttemptedAxiom variable)
returnList builtinListSort builtinListChild = do
    tools <- Simplifier.askMetadataTools
    Builtin.appliedFunction
        $ Reflection.give tools
        $ asPattern builtinListSort builtinListChild

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ resultSort =
        \case
            [elem'] -> returnList resultSort (Seq.singleton elem')
            _ -> Builtin.wrongArity elementKey

evalGet :: Builtin.Function
evalGet =
    Builtin.functionEvaluator evalGet0
  where
    evalGet0
        :: (Ord variable, SortedVariable variable, MonadSimplify simplifier)
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> simplifier (AttemptedAxiom variable)
    evalGet0 _ _ = \arguments ->
        Builtin.getAttemptedAxiom
        (do
            let (_list, _ix) =
                    case arguments of
                        [_list, _ix] -> (_list, _ix)
                        _ -> Builtin.wrongArity getKey
                emptyList = do
                    _list <- expectBuiltinList getKey _list
                    if Seq.null _list
                        then Builtin.appliedFunction Pattern.bottom
                        else empty
                bothConcrete = do
                    _list <- expectBuiltinList getKey _list
                    _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
                    let ix
                            | _ix < 0 =
                                -- negative indices count from end of list
                                _ix + Seq.length _list
                            | otherwise = _ix
                    (Builtin.appliedFunction . maybeBottom)
                        (Seq.lookup ix _list)
            emptyList <|> bothConcrete
        )
      where
        maybeBottom =
            maybe Pattern.bottom Pattern.fromTermLike

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ resultSort =
        \case
            [] -> returnList resultSort Seq.empty
            _ -> Builtin.wrongArity "LIST.unit"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0
        :: (Ord variable, SortedVariable variable, MonadSimplify simplifier)
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> simplifier (AttemptedAxiom variable)
    evalConcat0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_list1, _list2) =
                    case arguments of
                        [_list1, _list2] -> (_list1, _list2)
                        _ -> Builtin.wrongArity concatKey
                leftIdentity = do
                    _list1 <- expectBuiltinList concatKey _list1
                    if Seq.null _list1
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _list2
                        else
                            empty
                rightIdentity = do
                    _list2 <- expectBuiltinList concatKey _list2
                    if Seq.null _list2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _list1
                        else
                            empty
                bothConcrete = do
                    _list1 <- expectBuiltinList concatKey _list1
                    _list2 <- expectBuiltinList concatKey _list2
                    returnList resultSort (_list1 <> _list2)
            leftIdentity <|> rightIdentity <|> bothConcrete

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (concatKey, evalConcat)
        , (elementKey, evalElement)
        , (unitKey, evalUnit)
        , (getKey, evalGet)
        ]

{- | Render an 'Domain.InternalList' as a 'TermLike' domain value pattern.

 -}
asTermLike
    :: (Ord variable, SortedVariable variable, Unparse variable)
    => Domain.InternalList (TermLike variable)
    -> TermLike variable
asTermLike builtin
  | Seq.null list = unit
  | otherwise = foldr1 concat' (element <$> list)
  where
    Domain.InternalList { builtinListChild = list } = builtin
    Domain.InternalList { builtinListUnit = unitSymbol } = builtin
    Domain.InternalList { builtinListElement = elementSymbol } = builtin
    Domain.InternalList { builtinListConcat = concatSymbol } = builtin

    unit = mkApplySymbol unitSymbol []
    element elem' = mkApplySymbol elementSymbol [elem']
    concat' list1 list2 = mkApplySymbol concatSymbol [list1, list2]

{- | Render a 'Seq' as an expanded internal list pattern.
 -}
asInternal
    :: (Ord variable, SortedVariable variable)
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Seq (TermLike variable)
    -> TermLike variable
asInternal tools builtinListSort builtinListChild =
    (mkBuiltin . Domain.BuiltinList)
        Domain.InternalList
            { builtinListSort
            , builtinListUnit =
                Builtin.lookupSymbolUnit tools builtinListSort
            , builtinListElement =
                Builtin.lookupSymbolElement tools builtinListSort
            , builtinListConcat =
                Builtin.lookupSymbolConcat tools builtinListSort
            , builtinListChild
            }

{- | Render a 'Seq' as an extended domain value pattern.

See also: 'asPattern'

 -}
asPattern
    ::  ( Ord variable, SortedVariable variable
        , Given (SmtMetadataTools Attribute.Symbol)
        )
    => Sort
    -> Seq (TermLike variable)
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal tools resultSort
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = Reflection.given

internalize
    :: (Ord variable, SortedVariable variable)
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
internalize tools termLike@(App_ symbol args)
  | isSymbolUnit    symbol , [ ] <- args = asInternal' (Seq.fromList args)
  | isSymbolElement symbol , [_] <- args = asInternal' (Seq.fromList args)
  | isSymbolConcat  symbol =
    case args of
        [BuiltinList_ list1, arg2              ]
          | (null . Domain.builtinListChild) list1 -> arg2
        [arg1              , BuiltinList_ list2]
          | (null . Domain.builtinListChild) list2 -> arg1
        [BuiltinList_ list1, BuiltinList_ list2] ->
            asInternal' (Function.on (<>) Domain.builtinListChild list1 list2)
        _ -> termLike
  where
    asInternal' = asInternal tools (termLikeSort termLike)
internalize _ termLike = termLike

{- | Find the symbol hooked to @LIST.get@ in an indexed module.
 -}
lookupSymbolGet
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolGet = Builtin.lookupSymbol getKey

{- | Check if the given symbol is hooked to @LIST.concat@.
-}
isSymbolConcat :: Symbol -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @LIST.element@.
-}
isSymbolElement :: Symbol -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @LIST.unit@.
-}
isSymbolUnit :: Symbol -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

{- | Simplify the conjunction or equality of two concrete List domain values.

    When it is used for simplifying equality, one should separately solve the
    case ⊥ = ⊥. One should also throw away the term in the returned pattern.

    The lists are assumed to have the same sort, but this is not checked. If
    multiple lists are hooked to the same builtin domain, the verifier should
    reject the definition.
 -}
unifyEquals
    ::  forall variable unifier
    .   ( Show variable
        , Unparse variable
        , SortedVariable variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => SimplificationType
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyEquals
    simplificationType
    simplifyChild
    first
    second
  =
    unifyEquals0 first second
  where
    propagatePredicates
        :: Traversable t
        => t (Conditional variable a)
        -> Conditional variable (t a)
    propagatePredicates = sequenceA

    unifyEquals0
        :: TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)

    unifyEquals0 dv1@(Builtin_ (Domain.BuiltinList builtin1)) =
        \case
            dv2@(Builtin_ child2)
              | Domain.BuiltinList builtin2 <- child2 ->
                Monad.Trans.lift $ unifyEqualsConcrete builtin1 builtin2
              | otherwise ->
                (error . unlines)
                    [ "Cannot unify a builtin List domain value:"
                    , show dv1
                    , "with:"
                    , show dv2
                    , "This should have been a sort error."
                    ]
            app@(App_ symbol2 args2)
              | isSymbolConcat symbol2 ->
                Monad.Trans.lift $ case args2 of
                    [ Builtin_ (Domain.BuiltinList builtin2), x@(Var_ _) ] ->
                        unifyEqualsFramedRight builtin1 builtin2 x
                    [ x@(Var_ _), Builtin_ (Domain.BuiltinList builtin2) ] ->
                        unifyEqualsFramedLeft builtin1 x builtin2
                    [ _, _ ] ->
                        Builtin.unifyEqualsUnsolved
                            simplificationType
                            dv1
                            app
                    _ -> Builtin.wrongArity concatKey
              | otherwise -> empty
            _ -> empty

    unifyEquals0 pat1 =
        \case
            dv@(Builtin_ (Domain.BuiltinList _)) -> unifyEquals0 dv pat1
            _ -> empty

    unifyEqualsConcrete
        :: Domain.InternalList (TermLike variable)
        -> Domain.InternalList (TermLike variable)
        -> unifier (Pattern variable)
    unifyEqualsConcrete builtin1 builtin2
      | Seq.length list1 /= Seq.length list2 = bottomWithExplanation
      | otherwise = do
        tools <- Simplifier.askMetadataTools
        Reflection.give tools $ do
            unified <- sequence $ Seq.zipWith simplifyChild list1 list2
            let
                propagatedUnified = propagatePredicates unified
                result = asInternal tools builtinListSort <$> propagatedUnified
            return result
      where
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = list2 } = builtin2

    unifyEqualsFramedRight
        :: Domain.InternalList (TermLike variable)
        -> Domain.InternalList (TermLike variable)
        -> TermLike variable
        -> unifier (Pattern variable)
    unifyEqualsFramedRight
        builtin1
        builtin2
        frame2
      | Seq.length prefix2 > Seq.length list1 = bottomWithExplanation
      | otherwise =
        do
            tools <- Simplifier.askMetadataTools
            let listSuffix1 = asInternal tools builtinListSort suffix1
            prefixUnified <-
                unifyEqualsConcrete
                    builtin1 { Domain.builtinListChild = prefix1 }
                    builtin2
            suffixUnified <- simplifyChild frame2 listSuffix1
            let result = mkBuiltin internal1 <$ prefixUnified <* suffixUnified
            return result
      where
        internal1 = Domain.BuiltinList builtin1
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = prefix2 } = builtin2
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length prefix2

    unifyEqualsFramedLeft
        :: Domain.InternalList (TermLike variable)
        -> TermLike variable
        -> Domain.InternalList (TermLike variable)
        -> unifier (Pattern variable)
    unifyEqualsFramedLeft
        builtin1
        frame2
        builtin2
      | Seq.length suffix2 > Seq.length list1 = bottomWithExplanation
      | otherwise =
        do
            tools <- Simplifier.askMetadataTools
            let listPrefix1 = asInternal tools builtinListSort prefix1
            prefixUnified <- simplifyChild frame2 listPrefix1
            suffixUnified <-
                unifyEqualsConcrete
                    builtin1 { Domain.builtinListChild = suffix1 }
                    builtin2
            let result = mkBuiltin internal1 <$ prefixUnified <* suffixUnified
            return result
      where
        internal1 = Domain.BuiltinList builtin1
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = suffix2 } = builtin2
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length list1 - Seq.length suffix2
    bottomWithExplanation = do
        Monad.Unify.explainBottom
            "Cannot unify lists of different length."
            first
            second
        return Pattern.bottom

concatKey :: IsString s => s
concatKey = "LIST.concat"

elementKey :: IsString s => s
elementKey = "LIST.element"

unitKey :: IsString s => s
unitKey = "LIST.unit"

getKey :: IsString s => s
getKey = "LIST.get"
