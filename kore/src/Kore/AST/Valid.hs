{- |
Description : Constructors and patterns for verified Kore syntax trees
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.AST.Valid
    (
    -- * Utility functions for dealing with sorts
      getSort
    , forceSort
    , predicateSort
    , localInPattern
    , inPath
    , isObviouslyPredicate
    -- * Pure Kore pattern constructors
    , mkAnd
    , mkApp
    , mkBottom
    , mkCeil
    , mkDomainValue
    , mkEquals
    , mkExists
    , mkFloor
    , mkForall
    , mkIff
    , mkImplies
    , mkIn
    , mkNext
    , mkNot
    , mkOr
    , mkRewrites
    , mkTop
    , mkVar
    , mkSetVar
    , mkStringLiteral
    , mkCharLiteral
    , mkSort
    , mkSortVariable
    , mkInhabitant
    , varS
    , symS
    -- * Predicate constructors
    , mkBottom_
    , mkCeil_
    , mkEquals_
    , mkFloor_
    , mkIn_
    , mkTop_
    -- * Sentence constructors
    , mkAlias
    , mkAlias_
    , mkAxiom
    , mkAxiom_
    , mkSymbol
    , mkSymbol_
    -- * Application constructors
    , applyAlias
    , applyAlias_
    , applySymbol
    , applySymbol_
    -- * Pattern synonyms
    , pattern And_
    , pattern App_
    , pattern Bottom_
    , pattern Ceil_
    , pattern DV_
    , pattern Equals_
    , pattern Exists_
    , pattern Floor_
    , pattern Forall_
    , pattern Iff_
    , pattern Implies_
    , pattern In_
    , pattern Next_
    , pattern Not_
    , pattern Or_
    , pattern Rewrites_
    , pattern Top_
    , pattern Var_
    , pattern V
    , pattern StringLiteral_
    , pattern CharLiteral_
    -- * Re-exports
    , module Valid
    ) where

import           Control.Applicative
import           Control.Comonad
import qualified Control.Lens as Lens
import           Data.Align
import           Data.Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           Data.These
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Annotation.Valid as Valid
import           Kore.AST.Lens
import           Kore.AST.Pure
import           Kore.Domain.Class
import           Kore.Syntax.Definition
import           Kore.Unparser
                 ( Unparse, renderDefault, unparseToString )
import qualified Kore.Unparser as Unparse

-- | Get the 'Sort' of a 'PurePattern' from the 'Valid' annotation.
getSort
    :: Functor domain
    => PurePattern domain variable (Valid variable)
    -> Sort
getSort (extract -> Valid { patternSort }) = patternSort

-- | Attempts to modify p to have sort s.
forceSort
    ::  ( Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => Sort
    -> pattern'
    -> pattern'
forceSort forcedSort = Recursive.apo forceSortWorker
  where
    forceSortWorker original@(Recursive.project -> valid :< pattern') =
        (valid { patternSort = forcedSort } :<)
            (case valid of
                Valid { patternSort }
                  | patternSort == forcedSort    -> Left <$> pattern'
                  | patternSort == predicateSort -> forceSortWorkerPredicate
                  | otherwise                    -> illSorted
            )
      where
        illSorted =
            (error . unlines)
            [ "Could not force pattern to sort '"
                ++ unparseToString forcedSort ++ "':"
            , unparseToString original
            ]
        forceSortWorkerPredicate =
            case pattern' of
                -- Predicates: Force sort and stop.
                BottomF bottom' ->
                    BottomF bottom' { bottomSort = forcedSort }
                TopF top' ->
                    TopF top' { topSort = forcedSort }
                CeilF ceil' ->
                    CeilF (Left <$> ceil'')
                  where
                    ceil'' = ceil' { ceilResultSort = forcedSort }
                FloorF floor' ->
                    FloorF (Left <$> floor'')
                  where
                    floor'' = floor' { floorResultSort = forcedSort }
                EqualsF equals' ->
                    EqualsF (Left <$> equals'')
                  where
                    equals'' = equals' { equalsResultSort = forcedSort }
                InF in' ->
                    InF (Left <$> in'')
                  where
                    in'' = in' { inResultSort = forcedSort }
                -- Connectives: Force sort and recurse.
                AndF and' ->
                    AndF (Right <$> and'')
                  where
                    and'' = and' { andSort = forcedSort }
                OrF or' ->
                    OrF (Right <$> or'')
                  where
                    or'' = or' { orSort = forcedSort }
                IffF iff' ->
                    IffF (Right <$> iff'')
                  where
                    iff'' = iff' { iffSort = forcedSort }
                ImpliesF implies' ->
                    ImpliesF (Right <$> implies'')
                  where
                    implies'' = implies' { impliesSort = forcedSort }
                NotF not' ->
                    NotF (Right <$> not'')
                  where
                    not'' = not' { notSort = forcedSort }
                NextF next' ->
                    NextF (Right <$> next'')
                  where
                    next'' = next' { nextSort = forcedSort }
                RewritesF rewrites' ->
                    RewritesF (Right <$> rewrites'')
                  where
                    rewrites'' = rewrites' { rewritesSort = forcedSort }
                ExistsF exists' ->
                    ExistsF (Right <$> exists'')
                  where
                    exists'' = exists' { existsSort = forcedSort }
                ForallF forall' ->
                    ForallF (Right <$> forall'')
                  where
                    forall'' = forall' { forallSort = forcedSort }
                -- Rigid: These patterns should never have sort _PREDICATE{}.
                ApplicationF _ -> illSorted
                DomainValueF _ -> illSorted
                CharLiteralF _ -> illSorted
                StringLiteralF _ -> illSorted
                VariableF _ -> illSorted
                InhabitantF _ -> illSorted
                SetVariableF _ -> illSorted

{- | Call the argument function with two patterns whose sorts agree.

If one pattern is flexibly sorted, the result is the rigid sort of the other
pattern. If both patterns are flexibly sorted, then the result is
'predicateSort'. If both patterns have the same rigid sort, that is the
result. It is an error if the patterns are rigidly sorted but do not have the
same sort.

 -}
makeSortsAgree
    ::  ( Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => (pattern' -> pattern' -> Sort -> a)
    -> pattern'
    -> pattern'
    -> a
makeSortsAgree withPatterns = \pattern1 pattern2 ->
    let
        sort1 = getRigidSort pattern1
        sort2 = getRigidSort pattern2
        sort = fromMaybe predicateSort (sort1 <|> sort2)
        !pattern1' = forceSort sort pattern1
        !pattern2' = forceSort sort pattern2
    in
        withPatterns pattern1' pattern2' sort
{-# INLINE makeSortsAgree #-}

getRigidSort
    ::  ( Traversable domain
        , valid ~ Valid variable
        )
    => PurePattern domain variable valid
    -> Maybe Sort
getRigidSort pattern' =
    case getSort pattern' of
        sort
          | sort == predicateSort -> Nothing
          | otherwise -> Just sort

{- | Construct an 'And' pattern.
 -}
mkAnd
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
    -> pattern'
mkAnd = makeSortsAgree mkAndWorker
  where
    mkAndWorker andFirst andSecond andSort =
        asPurePattern (valid :< AndF and')
      where
        valid = Valid { patternSort = andSort, freeVariables }
        and' = And { andSort, andFirst, andSecond }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract andFirst
            Valid { freeVariables = freeVariables2 } = extract andSecond

{- | Construct an 'Application' pattern.

The result sort of the 'SymbolOrAlias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
-- TODO: Should this check for sort agreement?
mkApp
    ::  ( Functor domain
        , Ord variable
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => Sort
    -- ^ Result sort
    -> SymbolOrAlias
    -- ^ Application symbol or alias
    -> [pattern']
    -- ^ Application arguments
    -> pattern'
mkApp patternSort applicationSymbolOrAlias applicationChildren =
    asPurePattern (valid :< ApplicationF application)
  where
    valid = Valid { patternSort, freeVariables }
    application = Application { applicationSymbolOrAlias, applicationChildren }
    freeVariables =
        Set.unions (Valid.freeVariables . extract <$> applicationChildren)

{- | The 'Sort' substitution from applying the given sort parameters.
 -}
sortSubstitution
    :: [SortVariable]
    -> [Sort]
    -> Map.Map SortVariable Sort
sortSubstitution variables sorts =
    foldl' insertSortVariable Map.empty (align variables sorts)
  where
    insertSortVariable map' =
        \case
            These var sort -> Map.insert var sort map'
            This _ -> (error . unlines) ("Too few parameters." : expected)
            That _ -> (error . unlines) ("Too many parameters." : expected)
    expected =
        [ "Expected:"
        , renderDefault (Unparse.parameters variables)
        , "but found:"
        , renderDefault (Unparse.parameters sorts)
        ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applyAlias_', 'applySymbol', 'mkAlias'

 -}
applyAlias
    ::  ( Traversable domain
        , Ord variable
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => SentenceAlias pattern'
    -- ^ 'Alias' declaration
    -> [Sort]
    -- ^ 'Alias' sort parameters
    -> [pattern']
    -- ^ 'Application' arguments
    -> pattern'
applyAlias sentence params children =
    mkApp
        resultSort'
        symbolOrAlias
        children'
  where
    SentenceAlias { sentenceAliasAlias = alias } = sentence
    SentenceAlias { sentenceAliasResultSort } = sentence
    Alias { aliasConstructor } = alias
    Alias { aliasParams } = alias
    symbolOrAlias =
        SymbolOrAlias
            { symbolOrAliasConstructor = aliasConstructor
            , symbolOrAliasParams = params
            }
    substitution = sortSubstitution aliasParams params
    childSorts = substituteSortVariables substitution <$> sentenceAliasSorts
      where
        SentenceAlias { sentenceAliasSorts } = sentence
    resultSort' = substituteSortVariables substitution sentenceAliasResultSort
    children' = alignWith forceChildSort childSorts children
      where
        forceChildSort =
            \case
                These sort pattern' -> forceSort sort pattern'
                This _ -> (error . unlines) ("Too few arguments." : expected)
                That _ -> (error . unlines) ("Too many arguments." : expected)
        expected =
            [ "Expected:"
            , renderDefault (Unparse.arguments childSorts)
            , "but found:"
            , renderDefault (Unparse.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The 'Alias' must not be declared with sort parameters.

See also: 'mkApp', 'applyAlias'

 -}
applyAlias_
    ::  ( Traversable domain
        , Ord variable
        , Unparse pattern'
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => SentenceAlias pattern'
    -> [pattern']
    -> pattern'
applyAlias_ sentence = applyAlias sentence []

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applySymbol_', 'mkSymbol'

 -}
applySymbol
    ::  ( Traversable domain
        , Ord variable
        , Unparse pattern'
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => SentenceSymbol pattern''
    -- ^ 'Symbol' declaration
    -> [Sort]
    -- ^ 'Symbol' sort parameters
    -> [pattern']
    -- ^ 'Application' arguments
    -> pattern'
applySymbol sentence params children =
    mkApp
        resultSort'
        symbolOrAlias
        children'
  where
    SentenceSymbol { sentenceSymbolSymbol = symbol } = sentence
    SentenceSymbol { sentenceSymbolResultSort } = sentence
    Symbol { symbolConstructor } = symbol
    Symbol { symbolParams } = symbol
    symbolOrAlias =
        SymbolOrAlias
            { symbolOrAliasConstructor = symbolConstructor
            , symbolOrAliasParams = params
            }
    substitution = sortSubstitution symbolParams params
    resultSort' = substituteSortVariables substitution sentenceSymbolResultSort
    childSorts = substituteSortVariables substitution <$> sentenceSymbolSorts
      where
        SentenceSymbol { sentenceSymbolSorts } = sentence
    children' = alignWith forceChildSort childSorts children
      where
        forceChildSort =
            \case
                These sort pattern' -> forceSort sort pattern'
                This _ -> (error . unlines) ("Too few arguments." : expected)
                That _ -> (error . unlines) ("Too many arguments." : expected)
        expected =
            [ "Expected:"
            , renderDefault (Unparse.arguments childSorts)
            , "but found:"
            , renderDefault (Unparse.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The 'Symbol' must not be declared with sort parameters.

See also: 'mkApp', 'applySymbol'

 -}
applySymbol_
    ::  ( Traversable domain
        , Ord variable
        , Unparse pattern'
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => SentenceSymbol pattern''
    -> [pattern']
    -> pattern'
applySymbol_ sentence = applySymbol sentence []

{- | Construct a 'Bottom' pattern in the given sort.

See also: 'mkBottom_'

 -}
mkBottom
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => Sort
    -> PurePattern domain variable valid
mkBottom bottomSort =
    asPurePattern (valid :< BottomF bottom)
  where
    valid = Valid { patternSort = bottomSort, freeVariables = Set.empty }
    bottom = Bottom { bottomSort }

{- | Construct a 'Bottom' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkBottom' instead.

See also: 'mkBottom'

 -}
mkBottom_
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => PurePattern domain variable valid
mkBottom_ = mkBottom predicateSort

{- | Construct a 'Ceil' pattern in the given sort.

See also: 'mkCeil_'

 -}
mkCeil
    ::  ( Functor domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => Sort
    -> pattern'
    -> pattern'
mkCeil ceilResultSort ceilChild =
    asPurePattern (valid :< CeilF ceil)
  where
    Valid { patternSort = ceilOperandSort, freeVariables } = extract ceilChild
    valid = Valid { patternSort = ceilResultSort, freeVariables }
    ceil = Ceil { ceilOperandSort, ceilResultSort, ceilChild }

{- | Construct a 'Ceil' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkCeil'
instead.

See also: 'mkCeil'

 -}
mkCeil_
    :: ( Functor domain
       , valid ~ Valid variable
       , pattern' ~ PurePattern domain variable valid
       )
    => pattern'
    -> pattern'
mkCeil_ = mkCeil predicateSort

{- | Construct a 'DomainValue' pattern.
 -}
mkDomainValue
    ::  ( Foldable domain
        , Domain domain
        , Ord variable
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => domain pattern'
    -> pattern'
mkDomainValue domain =
    asPurePattern (valid :< DomainValueF domain)
  where
    freeVariables =
        (Set.unions . toList)
            (Valid.freeVariables . extract <$> domain)
    valid = Valid { patternSort = domainValueSort, freeVariables }
    DomainValue { domainValueSort } = Lens.view lensDomainValue domain

{- | Construct an 'Equals' pattern in the given sort.

See also: 'mkEquals_'

 -}
mkEquals
    ::  ( Ord variable
        , Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        , Unparse pattern'
        )
    => Sort
    -> pattern'
    -> pattern'
    -> pattern'
mkEquals equalsResultSort =
    makeSortsAgree mkEquals'Worker
  where
    mkEquals'Worker equalsFirst equalsSecond equalsOperandSort =
        asPurePattern (valid :< EqualsF equals)
      where
        valid = Valid { patternSort = equalsResultSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract equalsFirst
            Valid { freeVariables = freeVariables2 } = extract equalsSecond
        equals =
            Equals
                { equalsOperandSort
                , equalsResultSort
                , equalsFirst
                , equalsSecond
                }

{- | Construct a 'Equals' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkEquals' instead.

See also: 'mkEquals'

 -}
mkEquals_
    ::  ( Ord variable
        , Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        , Unparse pattern'
        )
    => pattern'
    -> pattern'
    -> pattern'
mkEquals_ = mkEquals predicateSort

{- | Construct an 'Exists' pattern.
 -}
mkExists
    ::  ( Ord variable
        , Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => variable
    -> pattern'
    -> pattern'
mkExists existsVariable existsChild =
    asPurePattern (valid :< ExistsF exists)
  where
    freeVariables =
        Set.delete existsVariable freeVariablesChild
      where
        Valid { freeVariables = freeVariablesChild } = extract existsChild
    valid = Valid { patternSort = existsSort, freeVariables }
    existsSort = getSort existsChild
    exists = Exists { existsSort, existsVariable, existsChild }

{- | Construct a 'Floor' pattern in the given sort.

See also: 'mkFloor_'

 -}
mkFloor
    ::  ( Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => Sort
    -> pattern'
    -> pattern'
mkFloor floorResultSort floorChild =
    asPurePattern (valid :< FloorF floor')
  where
    valid = Valid { patternSort = floorResultSort, freeVariables }
    Valid { patternSort = floorOperandSort, freeVariables } = extract floorChild
    floor' = Floor { floorOperandSort, floorResultSort, floorChild }

{- | Construct a 'Floor' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkFloor'
instead.

See also: 'mkFloor'

 -}
mkFloor_
    ::  ( Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
mkFloor_ = mkFloor predicateSort

{- | Construct a 'Forall' pattern.
 -}
mkForall
    ::  ( Ord variable
        , Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => variable
    -> pattern'
    -> pattern'
mkForall forallVariable forallChild =
    asPurePattern (valid :< ForallF forall)
  where
    valid = Valid { patternSort = forallSort, freeVariables }
    forallSort = getSort forallChild
    freeVariables =
        Set.delete forallVariable freeVariablesChild
      where
        Valid { freeVariables = freeVariablesChild } = extract forallChild
    forall = Forall { forallSort, forallVariable, forallChild }

{- | Construct an 'Iff' pattern.
 -}
mkIff
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
    -> pattern'
mkIff = makeSortsAgree mkIffWorker
  where
    mkIffWorker iffFirst iffSecond iffSort =
        asPurePattern (valid :< IffF iff')
      where
        valid = Valid { patternSort = iffSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract iffFirst
            Valid { freeVariables = freeVariables2 } = extract iffSecond
        iff' = Iff { iffSort, iffFirst, iffSecond }

{- | Construct an 'Implies' pattern.
 -}
mkImplies
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
    -> pattern'
mkImplies = makeSortsAgree mkImpliesWorker
  where
    mkImpliesWorker impliesFirst impliesSecond impliesSort =
        asPurePattern (valid :< ImpliesF implies')
      where
        valid = Valid { patternSort = impliesSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract impliesFirst
            Valid { freeVariables = freeVariables2 } = extract impliesSecond
        implies' = Implies { impliesSort, impliesFirst, impliesSecond }

{- | Construct a 'In' pattern in the given sort.

See also: 'mkIn_'

 -}
mkIn
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => Sort
    -> pattern'
    -> pattern'
    -> pattern'
mkIn inResultSort = makeSortsAgree mkInWorker
  where
    mkInWorker inContainedChild inContainingChild inOperandSort =
        asPurePattern (valid :< InF in')
      where
        valid = Valid { patternSort = inResultSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract inContainedChild
            Valid { freeVariables = freeVariables2 } = extract inContainingChild
        in' =
            In
                { inOperandSort
                , inResultSort
                , inContainedChild
                , inContainingChild
                }

{- | Construct a 'In' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkIn'
instead.

See also: 'mkIn'

 -}
mkIn_
    ::  ( Ord variable
        , Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        , Unparse pattern'
        )
    => pattern'
    -> pattern'
    -> pattern'
mkIn_ = mkIn predicateSort

{- | Construct a 'Next' pattern.
 -}
mkNext
    ::  ( Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
mkNext nextChild =
    asPurePattern (valid :< NextF next)
  where
    valid = Valid { patternSort = nextSort, freeVariables }
    Valid { patternSort = nextSort, freeVariables } = extract nextChild
    next = Next { nextSort, nextChild }

{- | Construct a 'Not' pattern.
 -}
mkNot
    ::  ( Traversable domain
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
mkNot notChild =
    asPurePattern (valid :< NotF not')
  where
    valid = Valid { patternSort = notSort, freeVariables }
    Valid { patternSort = notSort, freeVariables } = extract notChild
    not' = Not { notSort, notChild }

{- | Construct an 'Or' pattern.
 -}
mkOr
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
    -> pattern'
mkOr = makeSortsAgree mkOrWorker
  where
    mkOrWorker orFirst orSecond orSort =
        asPurePattern (valid :< OrF or')
      where
        valid = Valid { patternSort = orSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract orFirst
            Valid { freeVariables = freeVariables2 } = extract orSecond
        or' = Or { orSort, orFirst, orSecond }

{- | Construct a 'Rewrites' pattern.
 -}
mkRewrites
    ::  ( Ord variable
        , Traversable domain
        , Unparse pattern'
        , HasCallStack
        , valid ~ Valid variable
        , pattern' ~ PurePattern domain variable valid
        )
    => pattern'
    -> pattern'
    -> pattern'
mkRewrites = makeSortsAgree mkRewritesWorker
  where
    mkRewritesWorker rewritesFirst rewritesSecond rewritesSort =
        asPurePattern (valid :< RewritesF rewrites')
      where
        valid = Valid { patternSort = rewritesSort, freeVariables }
        freeVariables =
            Set.union freeVariables1 freeVariables2
          where
            Valid { freeVariables = freeVariables1 } = extract rewritesFirst
            Valid { freeVariables = freeVariables2 } = extract rewritesSecond
        rewrites' = Rewrites { rewritesSort, rewritesFirst, rewritesSecond }

{- | Construct a 'Top' pattern in the given sort.

See also: 'mkTop_'

 -}
mkTop
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => Sort
    -> PurePattern domain variable valid
mkTop topSort =
    asPurePattern (valid :< TopF top)
  where
    valid = Valid { patternSort = topSort, freeVariables = Set.empty }
    top = Top { topSort }

{- | Construct a 'Top' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkTop' instead.

See also: 'mkTop'

 -}
mkTop_
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => PurePattern domain variable valid
mkTop_ = mkTop predicateSort

{- | Construct a variable pattern.
 -}
mkVar
    ::  ( Functor domain
        , SortedVariable variable
        , valid ~ Valid variable
        )
    => variable
    -> PurePattern domain variable valid
mkVar var =
    asPurePattern (validVar var :< VariableF var)

validVar
    :: SortedVariable variable
    => variable
    -> Valid variable
validVar var = Valid { patternSort, freeVariables }
  where
    patternSort = sortedVariableSort var
    freeVariables = Set.singleton var

{- | Construct a set variable pattern.
 -}
mkSetVar
    ::  ( Functor domain
        , SortedVariable variable
        , valid ~ Valid variable
        )
    => variable
    -> PurePattern domain variable valid
mkSetVar var =
    asPurePattern (validVar var :< SetVariableF (SetVariable var))

{- | Construct a 'StringLiteral' pattern.
 -}
mkStringLiteral
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => Text
    -> PurePattern domain variable valid
mkStringLiteral string =
    asPurePattern (valid :< StringLiteralF stringLiteral)
  where
    valid = Valid { patternSort = stringMetaSort, freeVariables = Set.empty}
    stringLiteral = StringLiteral string

{- | Construct a 'CharLiteral' pattern.
 -}
mkCharLiteral
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => Char
    -> PurePattern domain variable valid
mkCharLiteral char =
    asPurePattern (valid :< CharLiteralF charLiteral)
  where
    valid = Valid { patternSort = charMetaSort, freeVariables = Set.empty }
    charLiteral = CharLiteral char

mkInhabitant
    ::  ( Functor domain
        , valid ~ Valid variable
        )
    => Sort
    -> PurePattern domain variable valid
mkInhabitant s =
    asPurePattern (valid :< InhabitantF s)
  where
    freeVariables = Set.empty
    patternSort = s
    valid = Valid { patternSort, freeVariables }

mkSort :: Id -> Sort
mkSort name = SortActualSort $ SortActual name []

mkSortVariable :: Id -> Sort
mkSortVariable name = SortVariableSort $ SortVariable name

-- | Construct a variable with a given name and sort
-- "x" `varS` s
varS :: Text -> Sort -> Variable
varS x variableSort =
    Variable
        { variableName = noLocationId x
        , variableSort
        , variableCounter = mempty
        }

-- | Construct a symbol with a given name and input sorts
-- "mult" `symS` [s, s]
-- Since the return sort is only found in MetadataTools, this is
-- mostly useful for testing.
symS :: Text -> [Sort] -> SymbolOrAlias
symS x s =
    SymbolOrAlias (noLocationId x) s

{- | Construct an axiom declaration with the given parameters and pattern.
 -}
mkAxiom
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain variable valid
        )
    => [SortVariable]
    -> patternType
    -> SentenceAxiom patternType
mkAxiom sentenceAxiomParameters sentenceAxiomPattern =
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes = Attributes []
        }

{- | Construct an axiom declaration with no parameters.

See also: 'mkAxiom'

 -}
mkAxiom_
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain variable valid
        )
    => patternType
    -> SentenceAxiom patternType
mkAxiom_ = mkAxiom []

{- | Construct a symbol declaration with the given parameters and sorts.
 -}
mkSymbol
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain variable valid
        , sortParam ~ SortVariable
        )
    => Id
    -> [sortParam]
    -> [Sort]
    -> Sort
    -> SentenceSymbol patternType
mkSymbol symbolConstructor symbolParams argumentSorts resultSort' =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Symbol
                { symbolConstructor
                , symbolParams
                }
        , sentenceSymbolSorts = argumentSorts
        , sentenceSymbolResultSort = resultSort'
        , sentenceSymbolAttributes = Attributes []
        }

{- | Construct a symbol declaration with no parameters.

See also: 'mkSymbol'

 -}
mkSymbol_
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain variable valid
        , sortParam ~ SortVariable
        )
    => Id
    -> [Sort]
    -> Sort
    -> SentenceSymbol patternType
mkSymbol_ symbolConstructor = mkSymbol symbolConstructor []

{- | Construct an alias declaration with the given parameters and sorts.
 -}
mkAlias
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain Variable valid
        , sortParam ~ SortVariable
        )
    => Id
    -> [sortParam]
    -> Sort
    -> [Variable]
    -> patternType
    -> SentenceAlias patternType
mkAlias aliasConstructor aliasParams resultSort' arguments right =
    SentenceAlias
        { sentenceAliasAlias =
            Alias
                { aliasConstructor
                , aliasParams
                }
        , sentenceAliasSorts = argumentSorts
        , sentenceAliasResultSort = resultSort'
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = aliasConstructor
                        , symbolOrAliasParams =
                            SortVariableSort <$> aliasParams
                        }
                , applicationChildren = arguments
                }
        , sentenceAliasRightPattern = right
        , sentenceAliasAttributes = Attributes []
        }
  where
    argumentSorts = variableSort <$> arguments

{- | Construct an alias declaration with no parameters.

See also: 'mkAlias'

 -}
mkAlias_
    ::  ( valid ~ Valid variable
        , patternType ~ PurePattern domain Variable valid
        , sortParam ~ SortVariable
        )
    => Id
    -> Sort
    -> [Variable]
    -> patternType
    -> SentenceAlias patternType
mkAlias_ aliasConstructor = mkAlias aliasConstructor []

pattern And_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern App_
    :: Functor dom
    => SymbolOrAlias
    -> [PurePattern dom var annotation]
    -> PurePattern dom var annotation

pattern Bottom_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation

pattern Ceil_
    :: Functor dom
    => Sort
    -> Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern DV_
  :: Domain dom
  => Sort
  -> dom (PurePattern dom var annotation)
  -> PurePattern dom var annotation

pattern Equals_
    :: Functor dom
    => Sort
    -> Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Exists_
    :: Functor dom
    => Sort
    -> var
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Floor_
    :: Functor dom
    => Sort
    -> Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Forall_
    :: Functor dom
    => Sort
    -> var
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Iff_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Implies_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern In_
    :: Functor dom
    => Sort
    -> Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Next_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Not_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Or_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation
    -> PurePattern dom var annotation

pattern Rewrites_
  :: Functor dom
  => Sort
  -> PurePattern dom var annotation
  -> PurePattern dom var annotation
  -> PurePattern dom var annotation

pattern Top_
    :: Functor dom
    => Sort
    -> PurePattern dom var annotation

pattern Var_
    :: Functor dom
    => var
    -> PurePattern dom var annotation

pattern StringLiteral_
  :: Functor dom
  => Text
  -> PurePattern dom var annotation

pattern CharLiteral_
  :: Functor dom
  => Char
  -> PurePattern dom var annotation

-- No way to make multiline pragma?
-- NOTE: If you add a case to the AST type, add another synonym here.
{-# COMPLETE And_, App_, Bottom_, Ceil_, DV_, Equals_, Exists_, Floor_, Forall_, Iff_, Implies_, In_, Next_, Not_, Or_, Rewrites_, Top_, Var_, StringLiteral_, CharLiteral_ #-}

pattern And_ andSort andFirst andSecond <-
    (Recursive.project -> _ :< AndF And { andSort, andFirst, andSecond })

pattern App_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplicationF Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )

pattern Bottom_ bottomSort <-
    (Recursive.project -> _ :< BottomF Bottom { bottomSort })

pattern Ceil_ ceilOperandSort ceilResultSort ceilChild <-
    (Recursive.project ->
        _ :< CeilF Ceil { ceilOperandSort, ceilResultSort, ceilChild }
    )

pattern DV_ domainValueSort domainValueChild <-
    (Recursive.project -> _ :< DomainValueF
        (Lens.view lensDomainValue ->
            DomainValue { domainValueSort, domainValueChild }
        )
    )

pattern Equals_ equalsOperandSort equalsResultSort equalsFirst equalsSecond <-
    (Recursive.project ->
        _ :< EqualsF Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
    )

pattern Exists_ existsSort existsVariable existsChild <-
    (Recursive.project ->
        _ :< ExistsF Exists { existsSort, existsVariable, existsChild }
    )

pattern Floor_ floorOperandSort floorResultSort floorChild <-
    (Recursive.project ->
        _ :< FloorF Floor
            { floorOperandSort
            , floorResultSort
            , floorChild
            }
    )

pattern Forall_ forallSort forallVariable forallChild <-
    (Recursive.project ->
        _ :< ForallF Forall { forallSort, forallVariable, forallChild }
    )

pattern Iff_ iffSort iffFirst iffSecond <-
    (Recursive.project ->
        _ :< IffF Iff { iffSort, iffFirst, iffSecond }
    )

pattern Implies_ impliesSort impliesFirst impliesSecond <-
    (Recursive.project ->
        _ :< ImpliesF Implies { impliesSort, impliesFirst, impliesSecond }
    )

pattern In_ inOperandSort inResultSort inFirst inSecond <-
    (Recursive.project ->
        _ :< InF In
            { inOperandSort
            , inResultSort
            , inContainedChild = inFirst
            , inContainingChild = inSecond
            }
    )

pattern Next_ nextSort nextChild <-
    (Recursive.project ->
        _ :< NextF Next { nextSort, nextChild })

pattern Not_ notSort notChild <-
    (Recursive.project ->
        _ :< NotF Not { notSort, notChild })

pattern Or_ orSort orFirst orSecond <-
    (Recursive.project -> _ :< OrF Or { orSort, orFirst, orSecond })

pattern Rewrites_ rewritesSort rewritesFirst rewritesSecond <-
    (Recursive.project ->
        _ :< RewritesF Rewrites
            { rewritesSort
            , rewritesFirst
            , rewritesSecond
            }
    )

pattern Top_ topSort <-
    (Recursive.project -> _ :< TopF Top { topSort })

pattern Var_ variable <-
    (Recursive.project -> _ :< VariableF variable)

pattern V
    :: Functor dom
    => var
    -> PurePattern dom var annotation
pattern V x <- Var_ x

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralF (StringLiteral str))

pattern CharLiteral_ char <-
    (Recursive.project -> _ :< CharLiteralF (CharLiteral char))
