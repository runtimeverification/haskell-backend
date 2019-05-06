{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.TermLike
    ( TermLike
    , freeVariables
    , termLikeSort
    , hasFreeVariable
    , withoutFreeVariable
    , mapVariables
    , traverseVariables
    , asConcreteStepPattern
    , fromConcreteStepPattern
    , substitute
    , externalizeFreshVariables
    -- * Utility functions for dealing with sorts
    , forceSort
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
    , SymbolOrAlias (..)
    , SortedVariable (..)
    , Id (..)
    , CofreeF (..), Comonad (..)
    , Variable (..)
    , Concrete
    , eraseAnnotations
    , module PatternF
    , module Kore.Sort
    ) where


import           Control.Applicative
import           Control.Comonad
import qualified Control.Lens as Lens
import           Control.Monad.Reader
                 ( Reader )
import qualified Control.Monad.Reader as Reader
import           Data.Align
import qualified Data.Foldable as Foldable
import           Data.Functor.Foldable
                 ( Base )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.These
import           GHC.Stack
                 ( HasCallStack )

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Domain.Builtin as Domain
import           Kore.Domain.Class
import           Kore.Sort
import qualified Kore.Substitute as Substitute
import           Kore.Syntax hiding
                 ( mapVariables, traverseVariables )
import           Kore.Syntax.Definition
import qualified Kore.Syntax.PatternF as PatternF
import qualified Kore.Syntax.Variable as Variable
import           Kore.Unparser
                 ( Unparse (..) )
import qualified Kore.Unparser as Unparse
import           Kore.Variables.Fresh

type TermLike variable =
    Pattern Domain.Builtin variable (Attribute.Pattern variable)

freeVariables :: TermLike variable -> Set variable
freeVariables termLike = Attribute.freeVariables (extract termLike)

hasFreeVariable
    :: Ord variable
    => variable
    -> TermLike variable
    -> Bool
hasFreeVariable variable = Set.member variable . freeVariables

{- | Throw an error if the variable occurs free in the pattern.

Otherwise, the argument is returned.

 -}
withoutFreeVariable
    ::  ( Ord variable
        , Unparse variable
        )
    => variable  -- ^ variable
    -> TermLike variable
    -> a  -- ^ result, if the variable does not occur free in the pattern
    -> a
withoutFreeVariable variable termLike result
  | hasFreeVariable variable termLike =
    (error . show . Pretty.vsep)
        [ Pretty.hsep
            [ "Unexpected free variable"
            , unparse variable
            , "in pattern:"
            ]
        , Pretty.indent 4 (unparse termLike)
        ]
  | otherwise = result

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> TermLike variable1
    -> TermLike variable2
mapVariables mapping =
    Recursive.unfold (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (valid :< pat) =
        Attribute.mapVariables mapping valid
        :< PatternF.mapVariables mapping pat

{- | Use the provided traversal to replace all variables in a 'TermLike'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> TermLike variable1
    -> m (TermLike variable2)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker (valid :< pat) =
        Recursive.embed <$> projected
      where
        projected =
            (:<)
                <$> Attribute.traverseVariables traversing valid
                <*> (PatternF.traverseVariables traversing =<< sequence pat)

{- | Construct a 'ConcreteStepPattern' from a 'TermLike'.

A concrete pattern contains no variables, so @asConcreteStepPattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcreteStepPattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcreteStepPattern
    :: TermLike variable
    -> Maybe (TermLike Concrete)
asConcreteStepPattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'TermLike' from a 'ConcreteStepPattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcreteStepPattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcreteStepPattern
    :: Ord variable
    => TermLike Concrete
    -> TermLike variable
fromConcreteStepPattern = mapVariables (\case {})

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
substitute
    ::  ( FreshVariable variable
        , Ord variable
        , SortedVariable variable
        )
    => Map variable (TermLike variable)
    -> TermLike variable
    -> TermLike variable
substitute = Substitute.substitute (Lens.lens getFreeVariables setFreeVariables)
  where
    getFreeVariables = Attribute.freeVariables
    setFreeVariables valid freeVars =
        valid { Attribute.freeVariables = freeVars }

{- | Reset the 'variableCounter' of all 'Variables'.

@externalizeFreshVariables@ resets the 'variableCounter' of all variables, while
ensuring that no 'Variable' in the result is accidentally captured.

 -}
externalizeFreshVariables :: TermLike Variable -> TermLike Variable
externalizeFreshVariables termLike =
    Reader.runReader
        (Recursive.fold externalizeFreshVariablesWorker termLike)
        renamedFreeVariables
  where
    -- | 'originalFreeVariables' are present in the original pattern; they do
    -- not have a generated counter. 'generatedFreeVariables' have a generated
    -- counter, usually because they were introduced by applying some axiom.
    (originalFreeVariables, generatedFreeVariables) =
        Set.partition Variable.isOriginalVariable (freeVariables termLike)

    -- | The map of generated free variables, renamed to be unique from the
    -- original free variables.
    (renamedFreeVariables, _) =
        Foldable.foldl' rename initial generatedFreeVariables
      where
        initial = (Map.empty, originalFreeVariables)
        rename (renaming, avoiding) variable =
            let
                variable' = safeVariable avoiding variable
                renaming' = Map.insert variable variable' renaming
                avoiding' = Set.insert variable' avoiding
            in
                (renaming', avoiding')

    {- | Look up a variable renaming.

    The original (not generated) variables of the pattern are never renamed, so
    these variables are not present in the Map of renamed variables.

     -}
    lookupVariable variable =
        Reader.asks (Map.lookup variable) >>= \case
            Nothing -> return variable
            Just variable' -> return variable'

    {- | Externalize a variable safely.

    The variable's counter is incremented until its externalized form is unique
    among the set of avoided variables. The externalized form is returned.

     -}
    safeVariable avoiding variable =
        head  -- 'head' is safe because 'iterate' creates an infinite list
        $ dropWhile wouldCapture
        $ Variable.externalizeFreshVariable
        <$> iterate nextVariable variable
      where
        wouldCapture var = Set.member var avoiding

    underBinder freeVariables' variable child = do
        let variable' = safeVariable freeVariables' variable
        child' <- Reader.local (Map.insert variable variable') child
        return (variable', child')

    externalizeFreshVariablesWorker
        ::  Base
                (TermLike Variable)
                (Reader
                    (Map Variable Variable)
                    (TermLike Variable)
                )
        ->  (Reader
                (Map Variable Variable)
                (TermLike Variable)
            )
    externalizeFreshVariablesWorker (valid :< patt) = do
        valid' <- Attribute.traverseVariables lookupVariable valid
        let freeVariables' = Attribute.freeVariables valid'
        patt' <-
            case patt of
                ExistsF exists -> do
                    let Exists { existsVariable, existsChild } = exists
                    (existsVariable', existsChild') <-
                        underBinder
                            freeVariables'
                            existsVariable
                            existsChild
                    let exists' =
                            exists
                                { existsVariable = existsVariable'
                                , existsChild = existsChild'
                                }
                    return (ExistsF exists')
                ForallF forall -> do
                    let Forall { forallVariable, forallChild } = forall
                    (forallVariable', forallChild') <-
                        underBinder
                            freeVariables'
                            forallVariable
                            forallChild
                    let forall' =
                            forall
                                { forallVariable = forallVariable'
                                , forallChild = forallChild'
                                }
                    return (ForallF forall')
                _ ->
                    PatternF.traverseVariables lookupVariable patt >>= sequence
        (return . Recursive.embed) (valid' :< patt')

-- | Get the 'Sort' of a 'TermLike' from the 'Attribute.Pattern' annotation.
termLikeSort :: TermLike variable -> Sort
termLikeSort = Attribute.patternSort . extract

-- | Attempts to modify p to have sort s.
forceSort
    :: (Unparse variable, HasCallStack)
    => Sort
    -> TermLike variable
    -> TermLike variable
forceSort forcedSort = Recursive.apo forceSortWorker
  where
    forceSortWorker original@(Recursive.project -> valid :< pattern') =
        (valid { Attribute.patternSort = forcedSort } :<)
            (case valid of
                Attribute.Pattern { patternSort = sort }
                  | sort == forcedSort    -> Left <$> pattern'
                  | sort == predicateSort -> forceSortWorkerPredicate
                  | otherwise             -> illSorted
            )
      where
        illSorted =
            (error . show . Pretty.vsep)
            [ Pretty.cat
                [ "Could not force pattern to sort "
                , Pretty.squotes (unparse forcedSort)
                , ":"
                ]
            , Pretty.indent 4 (unparse original)
            ]
        forceSortWorkerPredicate =
            case pattern' of
                -- Predicates: Force sort and stop.
                BottomF bottom' -> BottomF bottom' { bottomSort = forcedSort }
                TopF top' -> TopF top' { topSort = forcedSort }
                CeilF ceil' -> CeilF (Left <$> ceil'')
                  where
                    ceil'' = ceil' { ceilResultSort = forcedSort }
                FloorF floor' -> FloorF (Left <$> floor'')
                  where
                    floor'' = floor' { floorResultSort = forcedSort }
                EqualsF equals' -> EqualsF (Left <$> equals'')
                  where
                    equals'' = equals' { equalsResultSort = forcedSort }
                InF in' -> InF (Left <$> in'')
                  where
                    in'' = in' { inResultSort = forcedSort }
                -- Connectives: Force sort and recurse.
                AndF and' -> AndF (Right <$> and'')
                  where
                    and'' = and' { andSort = forcedSort }
                OrF or' -> OrF (Right <$> or'')
                  where
                    or'' = or' { orSort = forcedSort }
                IffF iff' -> IffF (Right <$> iff'')
                  where
                    iff'' = iff' { iffSort = forcedSort }
                ImpliesF implies' -> ImpliesF (Right <$> implies'')
                  where
                    implies'' = implies' { impliesSort = forcedSort }
                NotF not' -> NotF (Right <$> not'')
                  where
                    not'' = not' { notSort = forcedSort }
                NextF next' -> NextF (Right <$> next'')
                  where
                    next'' = next' { nextSort = forcedSort }
                RewritesF rewrites' -> RewritesF (Right <$> rewrites'')
                  where
                    rewrites'' = rewrites' { rewritesSort = forcedSort }
                ExistsF exists' -> ExistsF (Right <$> exists'')
                  where
                    exists'' = exists' { existsSort = forcedSort }
                ForallF forall' -> ForallF (Right <$> forall'')
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
    ::  ( Unparse variable
        , HasCallStack
        )
    => (TermLike variable -> TermLike variable -> Sort -> a)
    -> TermLike variable
    -> TermLike variable
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

getRigidSort :: TermLike variable -> Maybe Sort
getRigidSort pattern' =
    case termLikeSort pattern' of
        sort
          | sort == predicateSort -> Nothing
          | otherwise -> Just sort

{- | Construct an 'And' pattern.
 -}
mkAnd
    ::  ( Ord variable
        , Unparse variable
        , HasCallStack
        )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkAnd = makeSortsAgree mkAndWorker
  where
    mkAndWorker andFirst andSecond andSort =
        asPattern (valid :< AndF and')
      where
        valid =
            Attribute.Pattern
                { patternSort = andSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        and' = And { andSort, andFirst, andSecond }
        freeVariables1 = Attribute.freeVariables (extract andFirst)
        freeVariables2 = Attribute.freeVariables (extract andSecond)

{- | Construct an 'Application' pattern.

The result sort of the 'SymbolOrAlias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
-- TODO: Should this check for sort agreement?
mkApp
    :: Ord variable
    => Sort
    -- ^ Result sort
    -> SymbolOrAlias
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> TermLike variable
mkApp resultSort applicationSymbolOrAlias applicationChildren =
    asPattern (valid :< ApplicationF application)
  where
    valid =
        Attribute.Pattern
            { patternSort = resultSort
            , freeVariables = Set.unions (freeVariables <$> applicationChildren)
            }
    application = Application { applicationSymbolOrAlias, applicationChildren }

{- | The 'Sort' substitution from applying the given sort parameters.
 -}
sortSubstitution
    :: [SortVariable]
    -> [Sort]
    -> Map.Map SortVariable Sort
sortSubstitution variables sorts =
    Foldable.foldl' insertSortVariable Map.empty (align variables sorts)
  where
    insertSortVariable map' =
        \case
            These var sort -> Map.insert var sort map'
            This _ ->
                (error . show . Pretty.vsep) ("Too few parameters:" : expected)
            That _ ->
                (error . show . Pretty.vsep) ("Too many parameters:" : expected)
    expected =
        [ "Expected:"
        , Pretty.indent 4 (Unparse.parameters variables)
        , "but found:"
        , Pretty.indent 4 (Unparse.parameters sorts)
        ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applyAlias_', 'applySymbol', 'mkAlias'

 -}
applyAlias
    :: (Ord variable, Unparse variable, HasCallStack)
    => SentenceAlias (TermLike variable)
    -- ^ 'Alias' declaration
    -> [Sort]
    -- ^ 'Alias' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
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
                This _ ->
                    (error . show . Pretty.vsep)
                        ("Too few parameters:" : expected)
                That _ ->
                    (error . show . Pretty.vsep)
                        ("Too many parameters:" : expected)
        expected =
            [ "Expected:"
            , Pretty.indent 4 (Unparse.arguments childSorts)
            , "but found:"
            , Pretty.indent 4 (Unparse.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The 'Alias' must not be declared with sort parameters.

See also: 'mkApp', 'applyAlias'

 -}
applyAlias_
    ::  ( Ord variable
        , Unparse variable
        )
    => SentenceAlias (TermLike variable)
    -> [TermLike variable]
    -> TermLike variable
applyAlias_ sentence = applyAlias sentence []

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applySymbol_', 'mkSymbol'

 -}
applySymbol
    ::  ( Ord variable
        , Unparse variable
        )
    => SentenceSymbol pattern''
    -- ^ 'Symbol' declaration
    -> [Sort]
    -- ^ 'Symbol' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
applySymbol sentence params children =
    mkApp resultSort' symbolOrAlias children'
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
                This _ ->
                    (error . show . Pretty.vsep)
                        ("Too few parameters:" : expected)
                That _ ->
                    (error . show . Pretty.vsep)
                        ("Too many parameters:" : expected)
        expected =
            [ "Expected:"
            , Pretty.indent 4 (Unparse.arguments childSorts)
            , "but found:"
            , Pretty.indent 4 (Unparse.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The 'Symbol' must not be declared with sort parameters.

See also: 'mkApp', 'applySymbol'

 -}
applySymbol_
    :: (Ord variable, Unparse variable)
    => SentenceSymbol pattern''
    -> [TermLike variable]
    -> TermLike variable
applySymbol_ sentence = applySymbol sentence []

{- | Construct a 'Bottom' pattern in the given sort.

See also: 'mkBottom_'

 -}
mkBottom :: Sort -> TermLike variable
mkBottom bottomSort =
    asPattern (valid :< BottomF bottom)
  where
    valid =
        Attribute.Pattern
            { patternSort = bottomSort
            , freeVariables = Set.empty
            }
    bottom = Bottom { bottomSort }

{- | Construct a 'Bottom' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkBottom' instead.

See also: 'mkBottom'

 -}
mkBottom_ :: TermLike variable
mkBottom_ = mkBottom predicateSort

{- | Construct a 'Ceil' pattern in the given sort.

See also: 'mkCeil_'

 -}
mkCeil :: Sort -> TermLike variable -> TermLike variable
mkCeil ceilResultSort ceilChild =
    asPattern (valid :< CeilF ceil)
  where
    ceilOperandSort = termLikeSort ceilChild
    valid =
        Attribute.Pattern
            { patternSort = ceilResultSort
            , freeVariables = freeVariables ceilChild
            }
    ceil = Ceil { ceilOperandSort, ceilResultSort, ceilChild }

{- | Construct a 'Ceil' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkCeil'
instead.

See also: 'mkCeil'

 -}
mkCeil_ :: TermLike variable -> TermLike variable
mkCeil_ = mkCeil predicateSort

{- | Construct a 'DomainValue' pattern.
 -}
mkDomainValue
    :: Ord variable
    => Domain.Builtin (TermLike variable)
    -> TermLike variable
mkDomainValue domain =
    asPattern (valid :< DomainValueF domain)
  where
    valid =
        Attribute.Pattern
            { patternSort = domainValueSort
            , freeVariables =
                (Set.unions . Foldable.toList) (freeVariables <$> domain)
            }
    DomainValue { domainValueSort } = Lens.view lensDomainValue domain

{- | Construct an 'Equals' pattern in the given sort.

See also: 'mkEquals_'

 -}
mkEquals
    :: ( Ord variable , Unparse variable, HasCallStack )
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals equalsResultSort =
    makeSortsAgree mkEquals'Worker
  where
    mkEquals'Worker equalsFirst equalsSecond equalsOperandSort =
        asPattern (valid :< EqualsF equals)
      where
        valid =
            Attribute.Pattern
                { patternSort = equalsResultSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables equalsFirst
        freeVariables2 = freeVariables equalsSecond
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
        , Unparse variable
        , HasCallStack
        )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals_ = mkEquals predicateSort

{- | Construct an 'Exists' pattern.
 -}
mkExists
    :: Ord variable
    => variable
    -> TermLike variable
    -> TermLike variable
mkExists existsVariable existsChild =
    asPattern (valid :< ExistsF exists)
  where
    valid =
        Attribute.Pattern
            { patternSort = existsSort
            , freeVariables  = Set.delete existsVariable freeVariablesChild
            }
    existsSort = termLikeSort existsChild
    freeVariablesChild = freeVariables existsChild
    exists = Exists { existsSort, existsVariable, existsChild }

{- | Construct a 'Floor' pattern in the given sort.

See also: 'mkFloor_'

 -}
mkFloor
    :: Sort
    -> TermLike variable
    -> TermLike variable
mkFloor floorResultSort floorChild =
    asPattern (valid :< FloorF floor')
  where
    valid =
        Attribute.Pattern
            { patternSort = floorResultSort
            , freeVariables = freeVariables floorChild
            }
    floorOperandSort = termLikeSort floorChild
    floor' = Floor { floorOperandSort, floorResultSort, floorChild }

{- | Construct a 'Floor' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkFloor'
instead.

See also: 'mkFloor'

 -}
mkFloor_ :: TermLike variable -> TermLike variable
mkFloor_ = mkFloor predicateSort

{- | Construct a 'Forall' pattern.
 -}
mkForall
    :: Ord variable
    => variable
    -> TermLike variable
    -> TermLike variable
mkForall forallVariable forallChild =
    asPattern (valid :< ForallF forall)
  where
    valid =
        Attribute.Pattern
            { patternSort = forallSort
            , freeVariables =
                Set.delete forallVariable freeVariablesChild
            }
    forallSort = termLikeSort forallChild
    freeVariablesChild = freeVariables forallChild
    forall = Forall { forallSort, forallVariable, forallChild }

{- | Construct an 'Iff' pattern.
 -}
mkIff
    :: ( Ord variable , Unparse variable , HasCallStack )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIff = makeSortsAgree mkIffWorker
  where
    mkIffWorker iffFirst iffSecond iffSort =
        asPattern (valid :< IffF iff')
      where
        valid =
            Attribute.Pattern
                { patternSort = iffSort
                , freeVariables =  Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables iffFirst
        freeVariables2 = freeVariables iffSecond
        iff' = Iff { iffSort, iffFirst, iffSecond }

{- | Construct an 'Implies' pattern.
 -}
mkImplies
    :: ( Ord variable , Unparse variable , HasCallStack )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkImplies = makeSortsAgree mkImpliesWorker
  where
    mkImpliesWorker impliesFirst impliesSecond impliesSort =
        asPattern (valid :< ImpliesF implies')
      where
        valid =
            Attribute.Pattern
                { patternSort = impliesSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables impliesFirst
        freeVariables2 = freeVariables impliesSecond
        implies' = Implies { impliesSort, impliesFirst, impliesSecond }

{- | Construct a 'In' pattern in the given sort.

See also: 'mkIn_'

 -}
mkIn
    :: ( Ord variable , Unparse variable , HasCallStack )
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn inResultSort = makeSortsAgree mkInWorker
  where
    mkInWorker inContainedChild inContainingChild inOperandSort =
        asPattern (valid :< InF in')
      where
        valid =
            Attribute.Pattern
                { patternSort = inResultSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables inContainedChild
        freeVariables2 = freeVariables inContainingChild
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
    :: ( Ord variable , Unparse variable , HasCallStack )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn_ = mkIn predicateSort

{- | Construct a 'Next' pattern.
 -}
mkNext :: TermLike variable -> TermLike variable
mkNext nextChild =
    asPattern (valid :< NextF next)
  where
    valid =
        Attribute.Pattern
            { patternSort = nextSort
            , freeVariables = freeVariables nextChild
            }
    nextSort = termLikeSort nextChild
    next = Next { nextSort, nextChild }

{- | Construct a 'Not' pattern.
 -}
mkNot :: TermLike variable -> TermLike variable
mkNot notChild =
    asPattern (valid :< NotF not')
  where
    valid =
        Attribute.Pattern
            { patternSort = notSort
            , freeVariables = freeVariables notChild
            }
    notSort = termLikeSort notChild
    not' = Not { notSort, notChild }

{- | Construct an 'Or' pattern.
 -}
mkOr
    :: ( Ord variable , Unparse variable , HasCallStack )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkOr = makeSortsAgree mkOrWorker
  where
    mkOrWorker orFirst orSecond orSort =
        asPattern (valid :< OrF or')
      where
        valid =
            Attribute.Pattern
                { patternSort = orSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables orFirst
        freeVariables2 = freeVariables orSecond
        or' = Or { orSort, orFirst, orSecond }

{- | Construct a 'Rewrites' pattern.
 -}
mkRewrites
    :: ( Ord variable , Unparse variable , HasCallStack )
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkRewrites = makeSortsAgree mkRewritesWorker
  where
    mkRewritesWorker rewritesFirst rewritesSecond rewritesSort =
        asPattern (valid :< RewritesF rewrites')
      where
        valid =
            Attribute.Pattern
                { patternSort = rewritesSort
                , freeVariables = Set.union freeVariables1 freeVariables2
                }
        freeVariables1 = freeVariables rewritesFirst
        freeVariables2 = freeVariables rewritesSecond
        rewrites' = Rewrites { rewritesSort, rewritesFirst, rewritesSecond }

{- | Construct a 'Top' pattern in the given sort.

See also: 'mkTop_'

 -}
mkTop :: Sort -> TermLike variable
mkTop topSort =
    asPattern (valid :< TopF top)
  where
    valid =
        Attribute.Pattern
            { patternSort = topSort
            , freeVariables = Set.empty
            }
    top = Top { topSort }

{- | Construct a 'Top' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkTop' instead.

See also: 'mkTop'

 -}
mkTop_ :: TermLike variable
mkTop_ = mkTop predicateSort

{- | Construct a variable pattern.
 -}
mkVar :: SortedVariable variable => variable -> TermLike variable
mkVar var = asPattern (validVar var :< VariableF var)

validVar
    :: SortedVariable variable
    => variable
    -> Attribute.Pattern variable
validVar var =
    Attribute.Pattern
        { patternSort = sortedVariableSort var
        , freeVariables = Set.singleton var
        }

{- | Construct a set variable pattern.
 -}
mkSetVar :: SortedVariable variable => variable -> TermLike variable
mkSetVar var =
    asPattern (validVar var :< SetVariableF (SetVariable var))

{- | Construct a 'StringLiteral' pattern.
 -}
mkStringLiteral
    ::  ( Functor domain
        , valid ~ Attribute.Pattern variable
        )
    => Text
    -> Pattern domain variable valid
mkStringLiteral string =
    asPattern (valid :< StringLiteralF stringLiteral)
  where
    valid =
        Attribute.Pattern
            { patternSort = stringMetaSort
            , freeVariables = Set.empty
            }
    stringLiteral = StringLiteral string

{- | Construct a 'CharLiteral' pattern.
 -}
mkCharLiteral
    ::  ( Functor domain
        , valid ~ Attribute.Pattern variable
        )
    => Char
    -> Pattern domain variable valid
mkCharLiteral char =
    asPattern (valid :< CharLiteralF charLiteral)
  where
    valid = Attribute.Pattern { patternSort = charMetaSort, freeVariables = Set.empty }
    charLiteral = CharLiteral char

mkInhabitant
    ::  ( Functor domain
        , valid ~ Attribute.Pattern variable
        )
    => Sort
    -> Pattern domain variable valid
mkInhabitant sort =
    asPattern (valid :< InhabitantF sort)
  where
    valid =
        Attribute.Pattern
            { patternSort = sort
            , freeVariables = Set.empty
            }

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
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain variable valid
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
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain variable valid
        )
    => patternType
    -> SentenceAxiom patternType
mkAxiom_ = mkAxiom []

{- | Construct a symbol declaration with the given parameters and sorts.
 -}
mkSymbol
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain variable valid
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
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain variable valid
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
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain Variable valid
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
    ::  ( valid ~ Attribute.Pattern variable
        , patternType ~ Pattern domain Variable valid
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
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern App_
    :: Functor dom
    => SymbolOrAlias
    -> [Pattern dom var annotation]
    -> Pattern dom var annotation

pattern Bottom_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation

pattern Ceil_
    :: Functor dom
    => Sort
    -> Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern DV_
  :: Domain dom
  => Sort
  -> dom (Pattern dom var annotation)
  -> Pattern dom var annotation

pattern Equals_
    :: Functor dom
    => Sort
    -> Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Exists_
    :: Functor dom
    => Sort
    -> var
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Floor_
    :: Functor dom
    => Sort
    -> Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Forall_
    :: Functor dom
    => Sort
    -> var
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Iff_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Implies_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern In_
    :: Functor dom
    => Sort
    -> Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Next_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Not_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Or_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation
    -> Pattern dom var annotation
    -> Pattern dom var annotation

pattern Rewrites_
  :: Functor dom
  => Sort
  -> Pattern dom var annotation
  -> Pattern dom var annotation
  -> Pattern dom var annotation

pattern Top_
    :: Functor dom
    => Sort
    -> Pattern dom var annotation

pattern Var_
    :: Functor dom
    => var
    -> Pattern dom var annotation

pattern StringLiteral_
  :: Functor dom
  => Text
  -> Pattern dom var annotation

pattern CharLiteral_
  :: Functor dom
  => Char
  -> Pattern dom var annotation

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
    -> Pattern dom var annotation
pattern V x <- Var_ x

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralF (StringLiteral str))

pattern CharLiteral_ char <-
    (Recursive.project -> _ :< CharLiteralF (CharLiteral char))
