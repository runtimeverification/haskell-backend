{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.TermLike
    ( TermLikeF (..)
    , TermLike (..)
    , Evaluated (..)
    , Builtin
    , extractAttributes
    , isSimplified
    , Pattern.isConstructorLike
    , assertConstructorLikeKeys
    , markSimplified
    , markSimplifiedConditional
    , markSimplifiedMaybeConditional
    , setSimplified
    , forgetSimplified
    , simplifiedAttribute
    , isFunctionPattern
    , isFunctionalPattern
    , isDefinedPattern
    , hasConstructorLikeTop
    , freeVariables
    , refreshVariables
    , removeEvaluated
    , termLikeSort
    , hasFreeVariable
    , withoutFreeVariable
    , mapVariables
    , traverseVariables
    , asConcrete
    , isConcrete
    , fromConcrete
    , Substitute.substitute
    , externalizeFreshVariables
    , refreshElementBinder
    , refreshSetBinder
    , depth
    -- * Utility functions for dealing with sorts
    , forceSort
    , fullyOverrideSort
    -- * Pure Kore pattern constructors
    , mkAnd
    , mkApplyAlias
    , mkApplySymbol
    , mkBottom
    , mkInternalBytes
    , mkInternalBytes'
    , mkBuiltin
    , mkBuiltinList
    , mkBuiltinMap
    , mkBuiltinSet
    , mkCeil
    , mkDomainValue
    , mkEquals
    , mkExists
    , mkExistsN
    , mkFloor
    , mkForall
    , mkForallN
    , mkIff
    , mkImplies
    , mkIn
    , mkMu
    , mkNext
    , mkNot
    , mkNu
    , mkOr
    , mkRewrites
    , mkTop
    , mkVar
    , mkSetVar
    , mkElemVar
    , mkStringLiteral
    , mkSort
    , mkSortVariable
    , mkInhabitant
    , mkEvaluated
    , mkEndianness
    , mkSignedness
    , elemVarS
    , setVarS
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
    , symbolApplication
    -- * Pattern synonyms
    , pattern And_
    , pattern ApplyAlias_
    , pattern App_
    , pattern Bottom_
    , pattern InternalBytes_
    , pattern Builtin_
    , pattern BuiltinBool_
    , pattern BuiltinInt_
    , pattern BuiltinList_
    , pattern BuiltinMap_
    , pattern BuiltinSet_
    , pattern BuiltinString_
    , pattern Ceil_
    , pattern DV_
    , pattern Equals_
    , pattern Exists_
    , pattern Floor_
    , pattern Forall_
    , pattern Iff_
    , pattern Implies_
    , pattern In_
    , pattern Mu_
    , pattern Next_
    , pattern Not_
    , pattern Nu_
    , pattern Or_
    , pattern Rewrites_
    , pattern Top_
    , pattern Var_
    , pattern ElemVar_
    , pattern SetVar_
    , pattern StringLiteral_
    , pattern Evaluated_
    , pattern Endianness_
    , pattern Signedness_
    , pattern Inj_
    -- * Re-exports
    , module Kore.Internal.Variable
    , FreshVariable (..)
    , Symbol (..)
    , Alias (..)
    , SortedVariable (..)
    , module Kore.Syntax.Id
    , CofreeF (..), Comonad (..)
    , Sort (..), SortActual (..), SortVariable (..)
    , stringMetaSort
    , module Kore.Internal.Inj
    , module Kore.Internal.InternalBytes
    , module Kore.Syntax.And
    , module Kore.Syntax.Application
    , module Kore.Syntax.Bottom
    , module Kore.Syntax.Ceil
    , module Kore.Syntax.DomainValue
    , module Kore.Syntax.Equals
    , module Kore.Syntax.Exists
    , module Kore.Syntax.Floor
    , module Kore.Syntax.Forall
    , module Kore.Syntax.Iff
    , module Kore.Syntax.Implies
    , module Kore.Syntax.In
    , module Kore.Syntax.Inhabitant
    , module Kore.Syntax.Mu
    , module Kore.Syntax.Next
    , module Kore.Syntax.Not
    , module Kore.Syntax.Nu
    , module Kore.Syntax.Or
    , module Kore.Syntax.Rewrites
    , module Kore.Syntax.StringLiteral
    , module Kore.Syntax.Top
    , module Variable
    ) where

import Prelude.Kore

import Data.Align
import Data.ByteString
    ( ByteString
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.Functor.Const
    ( Const (..)
    )
import Data.Functor.Foldable
    ( Base
    )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map.Strict as Map
import Data.Monoid
    ( Endo (..)
    )
import Data.Set
    ( Set
    )
import Data.Text
    ( Text
    )
import Data.These

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Pattern.ConstructorLike as Pattern
import qualified Kore.Attribute.Pattern.Defined as Pattern
import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Pattern.Function as Pattern
import qualified Kore.Attribute.Pattern.Functional as Pattern
import qualified Kore.Attribute.Pattern.Simplified as Pattern
import Kore.Attribute.Synthetic
import Kore.Builtin.Endianness.Endianness
    ( Endianness
    )
import Kore.Builtin.Signedness.Signedness
    ( Signedness
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Error
import Kore.Internal.Alias
import Kore.Internal.Inj
import Kore.Internal.InternalBytes
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.Symbol hiding
    ( isConstructorLike
    )
import Kore.Internal.TermLike.TermLike
import Kore.Internal.Variable
import Kore.Sort
import qualified Kore.Substitute as Substitute
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.Definition hiding
    ( Alias
    , Symbol
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.DomainValue
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Id
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Inhabitant
import Kore.Syntax.Mu
import Kore.Syntax.Next
import Kore.Syntax.Not
import Kore.Syntax.Nu
import Kore.Syntax.Or
import Kore.Syntax.Rewrites
import Kore.Syntax.StringLiteral
import Kore.Syntax.Top
import Kore.Syntax.Variable as Variable
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Unparser as Unparser
import Kore.Variables.Binding
import Kore.Variables.Fresh
    ( FreshPartialOrd
    , FreshVariable
    )
import qualified Kore.Variables.Fresh as Fresh
import Kore.Variables.UnifiedVariable
import qualified Pretty

hasFreeVariable
    :: Ord variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Bool
hasFreeVariable variable = isFreeVariable variable . freeVariables

refreshVariables
    :: InternalVariable variable
    => FreeVariables variable
    -> TermLike variable
    -> TermLike variable
refreshVariables (FreeVariables.toSet -> avoid) term =
    Substitute.substitute subst term
  where
    rename = Fresh.refreshVariables avoid originalFreeVariables
    originalFreeVariables = FreeVariables.toSet (freeVariables term)
    subst = mkVar <$> rename

{- | Is the 'TermLike' a function pattern?
 -}
isFunctionPattern :: TermLike variable -> Bool
isFunctionPattern =
    Pattern.isFunction . Attribute.function . extractAttributes

{- | Does the 'TermLike' have a constructor-like top?

A pattern is 'ConstructorLikeTop' if it is one of the following:

- A 'StringLiteral'
- A 'DomainValue'
- A 'Builtin'
- An 'Application' whose head is a constructor symbol
 -}
hasConstructorLikeTop :: TermLike variable -> Bool
hasConstructorLikeTop = \case
    App_ symbol _ -> isConstructor symbol
    DV_ _ _ -> True
    BuiltinBool_ _ -> True
    BuiltinInt_ _ -> True
    BuiltinList_ _ -> True
    BuiltinMap_ _ -> True
    BuiltinSet_ _ -> True
    BuiltinString_ _ -> True
    StringLiteral_ _ -> True
    _ -> False

{- | Is the 'TermLike' functional?
 -}
isFunctionalPattern :: TermLike variable -> Bool
isFunctionalPattern =
    Pattern.isFunctional . Attribute.functional . extractAttributes

{- | Is the 'TermLike' defined, i.e. known not to be 'Bottom'?
 -}
isDefinedPattern :: TermLike variable -> Bool
isDefinedPattern =
    Pattern.isDefined . Attribute.defined . extractAttributes

{- | Throw an error if the variable occurs free in the pattern.

Otherwise, the argument is returned.

 -}
withoutFreeVariable
    :: InternalVariable variable
    => UnifiedVariable variable  -- ^ variable
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

{- | Construct a @'TermLike' 'Concrete'@ from any 'TermLike'.

A concrete pattern contains no variables, so @asConcreteStepPattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcrete@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcrete
    :: Ord variable
    => TermLike variable
    -> Maybe (TermLike Concrete)
asConcrete = traverseVariables (\case { _ -> Nothing }) (\case { _ -> Nothing })

isConcrete :: Ord variable => TermLike variable -> Bool
isConcrete = isJust . asConcrete

{- | Construct any 'TermLike' from a @'TermLike' 'Concrete'@.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcrete@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcrete
    :: (FreshPartialOrd variable, SortedVariable variable)
    => TermLike Concrete
    -> TermLike variable
fromConcrete = mapVariables (\case {}) (\case {})

isSimplified :: SideCondition.Representation -> TermLike variable -> Bool
isSimplified sideCondition =
    Attribute.isSimplified sideCondition . extractAttributes

{- | Forget the 'simplifiedAttribute' associated with the 'TermLike'.

@
isSimplified (forgetSimplified _) == False
@

 -}
forgetSimplified
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
forgetSimplified = resynthesize

isFullySimplified :: TermLike variable -> Bool
isFullySimplified = Attribute.isFullySimplified . extractAttributes

simplifiedAttribute :: TermLike variable -> Pattern.Simplified
simplifiedAttribute = Attribute.simplifiedAttribute . extractAttributes

assertConstructorLikeKeys
    :: InternalVariable variable
    => Foldable t
    => t (TermLike variable)
    -> a
    -> a
assertConstructorLikeKeys keys a
    | any (not . Pattern.isConstructorLike) keys =
        let simplifiableKeys =
                filter (not . Pattern.isConstructorLike) $ Foldable.toList keys
        in
            (error . show . Pretty.vsep) $
                [ "Map and Set may only contain constructor-like \
                  \keys (resp. elements)."
                , Pretty.indent 2 "Simplifiable keys:"
                ]
                <> fmap (Pretty.indent 4 . unparse) simplifiableKeys
    | any (not . isFullySimplified) keys =
        let simplifiableKeys =
                filter (not . isFullySimplified) $ Foldable.toList keys
        in
            (error . show . Pretty.vsep) $
                [ "Map and Set may only contain simplified \
                  \keys."
                , Pretty.indent 2 "Simplifiable keys:"
                ]
                <> fmap (Pretty.indent 4 . unparse) simplifiableKeys
    | otherwise = a

{- | Mark a 'TermLike' as fully simplified at the current level.

The pattern is fully simplified if we do not know how to simplify it any
further. The simplifier reserves the right to skip any pattern which is marked,
so do not mark any pattern unless you are certain it cannot be further
simplified.

Note that fully simplified at the current level may not mean that the pattern
is fully simplified (e.g. if a child is simplified conditionally).

-}
markSimplified
    :: (HasCallStack, InternalVariable variable)
    => TermLike variable -> TermLike variable
markSimplified (Recursive.project -> attrs :< termLikeF) =
    Recursive.embed
        (  Attribute.setSimplified
            (checkedSimplifiedFromChildren termLikeF)
            attrs
        :< termLikeF
        )

markSimplifiedMaybeConditional
    :: (HasCallStack, InternalVariable variable)
    => Maybe SideCondition.Representation
    -> TermLike variable
    -> TermLike variable
markSimplifiedMaybeConditional Nothing = markSimplified
markSimplifiedMaybeConditional (Just condition) =
    markSimplifiedConditional condition

cannotSimplifyNotSimplifiedError
    :: (HasCallStack, InternalVariable variable)
    => TermLikeF variable (TermLike variable) -> a
cannotSimplifyNotSimplifiedError termLikeF =
    error
        (  "Unexpectedly marking term with NotSimplified children as \
            \simplified:\n"
        ++ show termLikeF
        ++ "\n"
        ++ Unparser.unparseToString termLikeF
        )

setSimplified
    :: (HasCallStack, InternalVariable variable)
    => Pattern.Simplified -> TermLike variable -> TermLike variable
setSimplified
    simplified
    (Recursive.project -> attrs :< termLikeF)
  =
    Recursive.embed
        (  Attribute.setSimplified mergedSimplified attrs
        :< termLikeF
        )
  where
    childSimplified = simplifiedFromChildren termLikeF
    mergedSimplified = case (childSimplified, simplified) of
        (Pattern.NotSimplified, Pattern.NotSimplified) -> Pattern.NotSimplified
        (Pattern.NotSimplified, _) -> cannotSimplifyNotSimplifiedError termLikeF
        (_, Pattern.NotSimplified) -> Pattern.NotSimplified
        _ -> childSimplified <> simplified

{-|Marks a term as being simplified as long as the side condition stays
unchanged.
-}
markSimplifiedConditional
    :: (HasCallStack, InternalVariable variable)
    => SideCondition.Representation -> TermLike variable -> TermLike variable
markSimplifiedConditional
    condition
    (Recursive.project -> attrs :< termLikeF)
  =
    Recursive.embed
        (  Attribute.setSimplified
                (  checkedSimplifiedFromChildren termLikeF
                <> Pattern.simplifiedConditionally condition
                )
                attrs
        :< termLikeF
        )

simplifiedFromChildren
    :: HasCallStack
    => TermLikeF variable (TermLike variable) -> Pattern.Simplified
simplifiedFromChildren termLikeF =
    case mergedSimplified of
        Pattern.NotSimplified -> Pattern.NotSimplified
        _ -> mergedSimplified `Pattern.simplifiedTo` Pattern.fullySimplified
  where
    mergedSimplified =
        foldMap (Attribute.simplifiedAttribute . extractAttributes) termLikeF

checkedSimplifiedFromChildren
    :: (HasCallStack, InternalVariable variable)
    => TermLikeF variable (TermLike variable) -> Pattern.Simplified
checkedSimplifiedFromChildren termLikeF =
    case simplifiedFromChildren termLikeF of
        Pattern.NotSimplified -> cannotSimplifyNotSimplifiedError termLikeF
        simplified -> simplified

-- | Get the 'Sort' of a 'TermLike' from the 'Attribute.Pattern' annotation.
termLikeSort :: TermLike variable -> Sort
termLikeSort = Attribute.patternSort . extractAttributes

-- | Attempts to modify p to have sort s.
forceSort
    :: (InternalVariable variable, HasCallStack)
    => Sort
    -> TermLike variable
    -> TermLike variable
forceSort forcedSort =
    if forcedSort == predicateSort
        then id
        else Recursive.apo forceSortWorker
  where
    forceSortWorker original@(Recursive.project -> attrs :< pattern') =
        (:<)
            (attrs { Attribute.patternSort = forcedSort })
            (case attrs of
                Attribute.Pattern { patternSort = sort }
                  | sort == forcedSort    -> Left <$> pattern'
                  | sort == predicateSort ->
                    forceSortPredicate forcedSort original
                  | otherwise             -> illSorted forcedSort original
            )

{-| Attempts to modify the pattern to have the given sort, ignoring the
previous sort and without assuming that the pattern's sorts are consistent.
-}
fullyOverrideSort
    :: forall variable
    .  (InternalVariable variable, HasCallStack)
    => Sort
    -> TermLike variable
    -> TermLike variable
fullyOverrideSort forcedSort = Recursive.apo overrideSortWorker
  where
    overrideSortWorker
        :: TermLike variable
        -> Base
            (TermLike variable)
            (Either (TermLike variable) (TermLike variable))
    overrideSortWorker original@(Recursive.project -> attrs :< _) =
        (:<)
            (attrs { Attribute.patternSort = forcedSort })
            (forceSortPredicate forcedSort original)

illSorted
    :: (InternalVariable variable, HasCallStack)
    => Sort -> TermLike variable -> a
illSorted forcedSort original =
    (error . show . Pretty.vsep)
    [ Pretty.cat
        [ "Could not force pattern to sort "
        , Pretty.squotes (unparse forcedSort)
        , ", instead it has sort "
        , Pretty.squotes (unparse (termLikeSort original))
        , ":"
        ]
    , Pretty.indent 4 (unparse original)
    ]

forceSortPredicate
    :: (InternalVariable variable, HasCallStack)
    => Sort
    -> TermLike variable
    -> TermLikeF variable (Either (TermLike variable) (TermLike variable))
forceSortPredicate
    forcedSort
    original@(Recursive.project -> _ :< pattern')
  =
    case pattern' of
        -- Recurse
        EvaluatedF evaluated -> EvaluatedF (Right <$> evaluated)
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
        MuF _ -> illSorted forcedSort original
        NuF _ -> illSorted forcedSort original
        ApplySymbolF _ -> illSorted forcedSort original
        ApplyAliasF _ -> illSorted forcedSort original
        BuiltinF _ -> illSorted forcedSort original
        DomainValueF _ -> illSorted forcedSort original
        StringLiteralF _ -> illSorted forcedSort original
        VariableF _ -> illSorted forcedSort original
        InternalBytesF _ -> illSorted forcedSort original
        InhabitantF _ -> illSorted forcedSort original
        EndiannessF _ -> illSorted forcedSort original
        SignednessF _ -> illSorted forcedSort original
        InjF _ -> illSorted forcedSort original

{- | Call the argument function with two patterns whose sorts agree.

If one pattern is flexibly sorted, the result is the rigid sort of the other
pattern. If both patterns are flexibly sorted, then the result is
'predicateSort'. If both patterns have the same rigid sort, that is the
result. It is an error if the patterns are rigidly sorted but do not have the
same sort.

 -}
makeSortsAgree
    :: (InternalVariable variable, HasCallStack)
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
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkAnd t1 t2 = updateCallStack $ makeSortsAgree mkAndWorker t1 t2
  where
    mkAndWorker andFirst andSecond andSort =
        synthesize (AndF And { andSort, andFirst, andSecond })

{- | Force the 'TermLike's to conform to their 'Sort's.

It is an error if the lists are not the same length, or if any 'TermLike' cannot
be coerced to its corresponding 'Sort'.

See also: 'forceSort'

 -}
forceSorts
    :: HasCallStack
    => InternalVariable variable
    => [Sort]
    -> [TermLike variable]
    -> [TermLike variable]
forceSorts operandSorts children =
    alignWith forceTheseSorts operandSorts children
  where
    forceTheseSorts (This _) =
        (error . show . Pretty.vsep) ("Too few arguments:" : expected)
    forceTheseSorts (That _) =
        (error . show . Pretty.vsep) ("Too many arguments:" : expected)
    forceTheseSorts (These sort termLike) = forceSort sort termLike
    expected =
        [ "Expected:"
        , Pretty.indent 4 (Unparser.arguments operandSorts)
        , "but found:"
        , Pretty.indent 4 (Unparser.arguments children)
        ]

{- | Remove `Evaluated` if it appears on the top of the `TermLike`.
-}
removeEvaluated :: TermLike variable -> TermLike variable
removeEvaluated termLike@(Recursive.project -> (_ :< termLikeF)) =
    case termLikeF of
        EvaluatedF (Evaluated e) -> removeEvaluated e
        _                        -> termLike

{- | Construct an 'Application' pattern.

The result sort of the 'Alias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
mkApplyAlias
    :: HasCallStack
    => InternalVariable variable
    => Alias (TermLike Variable)
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> TermLike variable
mkApplyAlias alias children =
    updateCallStack $ synthesize (ApplyAliasF application)
  where
    application =
        Application
            { applicationSymbolOrAlias = alias
            , applicationChildren = forceSorts operandSorts children
            }
    operandSorts = applicationSortsOperands (aliasSorts alias)

{- | Construct an 'Application' pattern.

The result sort of the 'SymbolOrAlias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
mkApplySymbol
    :: HasCallStack
    => InternalVariable variable
    => Symbol
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> TermLike variable
mkApplySymbol symbol children =
    updateCallStack
    $ synthesize (ApplySymbolF (symbolApplication symbol children))

symbolApplication
    :: HasCallStack
    => InternalVariable variable
    => Symbol
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> Application Symbol (TermLike variable)
symbolApplication symbol children =
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = forceSorts operandSorts children
        }
  where
    operandSorts = applicationSortsOperands (symbolSorts symbol)

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApplyAlias', 'applyAlias_', 'applySymbol', 'mkAlias'

 -}
applyAlias
    :: HasCallStack
    => InternalVariable variable
    => SentenceAlias (TermLike Variable)
    -- ^ 'Alias' declaration
    -> [Sort]
    -- ^ 'Alias' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
applyAlias sentence params children =
    updateCallStack $ mkApplyAlias internal children'
  where
    SentenceAlias { sentenceAliasAlias = external } = sentence
    Syntax.Alias { aliasConstructor } = external
    Syntax.Alias { aliasParams } = external
    internal =
        Alias
            { aliasConstructor
            , aliasParams = params
            , aliasSorts =
                symbolOrAliasSorts params sentence
                & assertRight
            , aliasLeft =
                applicationChildren
                . sentenceAliasLeftPattern
                $ sentence
            , aliasRight = sentenceAliasRightPattern sentence
            }
    substitution = sortSubstitution aliasParams params
    childSorts = substituteSortVariables substitution <$> sentenceAliasSorts
      where
        SentenceAlias { sentenceAliasSorts } = sentence
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
            , Pretty.indent 4 (Unparser.arguments childSorts)
            , "but found:"
            , Pretty.indent 4 (Unparser.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The 'Alias' must not be declared with sort parameters.

See also: 'mkApp', 'applyAlias'

 -}
applyAlias_
    :: HasCallStack
    => InternalVariable variable
    => SentenceAlias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable
applyAlias_ sentence = updateCallStack . applyAlias sentence []

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applySymbol_', 'mkSymbol'

 -}
applySymbol
    :: HasCallStack
    => InternalVariable variable
    => SentenceSymbol pattern''
    -- ^ 'Symbol' declaration
    -> [Sort]
    -- ^ 'Symbol' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
applySymbol sentence params children =
    updateCallStack $ mkApplySymbol internal children
  where
    SentenceSymbol { sentenceSymbolSymbol = external } = sentence
    Syntax.Symbol { symbolConstructor } = external
    internal =
        Symbol
            { symbolConstructor
            , symbolParams = params
            , symbolAttributes = Default.def
            , symbolSorts =
                symbolOrAliasSorts params sentence
                & assertRight
            }

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The 'Symbol' must not be declared with sort parameters.

See also: 'mkApplySymbol', 'applySymbol'

 -}
applySymbol_
    :: HasCallStack
    => InternalVariable variable
    => SentenceSymbol pattern''
    -> [TermLike variable]
    -> TermLike variable
applySymbol_ sentence = updateCallStack . applySymbol sentence []

{- | Construct a 'Bottom' pattern in the given sort.

See also: 'mkBottom_'

 -}
mkBottom
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
mkBottom bottomSort =
    updateCallStack $ synthesize (BottomF Bottom { bottomSort })

{- | Construct a 'Bottom' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use
'mkBottom' instead.

See also: 'mkBottom'

 -}
mkBottom_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
mkBottom_ = updateCallStack $ mkBottom predicateSort

{- | Construct a 'Ceil' pattern in the given sort.

See also: 'mkCeil_'

 -}
mkCeil
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
mkCeil ceilResultSort ceilChild =
    updateCallStack
        $ synthesize (CeilF Ceil { ceilOperandSort, ceilResultSort, ceilChild })
  where
    ceilOperandSort = termLikeSort ceilChild

{- | Construct a 'Ceil' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use 'mkCeil'
instead.

See also: 'mkCeil'

 -}
mkCeil_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
mkCeil_ = updateCallStack . mkCeil predicateSort

{- | Construct a builtin pattern.
 -}
mkBuiltin
    :: HasCallStack
    => InternalVariable variable
    => Domain.Builtin (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltin = updateCallStack . synthesize . BuiltinF

{- | Construct a builtin list pattern.
 -}
mkBuiltinList
    :: HasCallStack
    => InternalVariable variable
    => Domain.InternalList (TermLike variable)
    -> TermLike variable
mkBuiltinList = updateCallStack . synthesize . BuiltinF . Domain.BuiltinList

{- | Construct a builtin map pattern.
 -}
mkBuiltinMap
    :: HasCallStack
    => InternalVariable variable
    => Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltinMap = updateCallStack . synthesize . BuiltinF . Domain.BuiltinMap

{- | Construct a builtin set pattern.
 -}
mkBuiltinSet
    :: HasCallStack
    => InternalVariable variable
    => Domain.InternalSet (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltinSet = updateCallStack . synthesize . BuiltinF . Domain.BuiltinSet

{- | Construct a 'DomainValue' pattern.
 -}
mkDomainValue
    :: HasCallStack
    => InternalVariable variable
    => DomainValue Sort (TermLike variable)
    -> TermLike variable
mkDomainValue = updateCallStack . synthesize . DomainValueF

{- | Construct an 'Equals' pattern in the given sort.

See also: 'mkEquals_'

 -}
mkEquals
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals equalsResultSort t1 =
    updateCallStack . makeSortsAgree mkEqualsWorker t1
  where
    mkEqualsWorker equalsFirst equalsSecond equalsOperandSort =
        synthesize (EqualsF equals)
      where
        equals =
            Equals
                { equalsOperandSort
                , equalsResultSort
                , equalsFirst
                , equalsSecond
                }

{- | Construct a 'Equals' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use
'mkEquals' instead.

See also: 'mkEquals'

 -}
mkEquals_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals_ t1 t2 = updateCallStack $ mkEquals predicateSort t1 t2

{- | Construct an 'Exists' pattern.
 -}
mkExists
    :: HasCallStack
    => InternalVariable variable
    => ElementVariable variable
    -> TermLike variable
    -> TermLike variable
mkExists existsVariable existsChild =
    updateCallStack
        $ synthesize (ExistsF Exists { existsSort, existsVariable, existsChild })
  where
    existsSort = termLikeSort existsChild

{- | Construct a sequence of 'Exists' patterns over several variables.
 -}
mkExistsN
    :: HasCallStack
    => InternalVariable variable
    => Foldable foldable
    => foldable (ElementVariable variable)
    -> TermLike variable
    -> TermLike variable
mkExistsN = (updateCallStack .) . appEndo . foldMap (Endo . mkExists)

{- | Construct a 'Floor' pattern in the given sort.

See also: 'mkFloor_'

 -}
mkFloor
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
mkFloor floorResultSort floorChild =
    updateCallStack
        $ synthesize (FloorF Floor { floorOperandSort, floorResultSort, floorChild })
  where
    floorOperandSort = termLikeSort floorChild

{- | Construct a 'Floor' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use 'mkFloor'
instead.

See also: 'mkFloor'

 -}
mkFloor_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
mkFloor_ = updateCallStack . mkFloor predicateSort

{- | Construct a 'Forall' pattern.
 -}
mkForall
    :: HasCallStack
    => InternalVariable variable
    => ElementVariable variable
    -> TermLike variable
    -> TermLike variable
mkForall forallVariable forallChild =
    updateCallStack
        $ synthesize (ForallF Forall { forallSort, forallVariable, forallChild })
  where
    forallSort = termLikeSort forallChild

{- | Construct a sequence of 'Forall' patterns over several variables.
 -}
mkForallN
    :: HasCallStack
    => InternalVariable variable
    => Foldable foldable
    => foldable (ElementVariable variable)
    -> TermLike variable
    -> TermLike variable
mkForallN = (updateCallStack .) . appEndo . foldMap (Endo . mkForall)

{- | Construct an 'Iff' pattern.
 -}
mkIff
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIff t1 t2 = updateCallStack $ makeSortsAgree mkIffWorker t1 t2
  where
    mkIffWorker iffFirst iffSecond iffSort =
        synthesize (IffF Iff { iffSort, iffFirst, iffSecond })

{- | Construct an 'Implies' pattern.
 -}
mkImplies
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkImplies t1 t2 = updateCallStack $ makeSortsAgree mkImpliesWorker t1 t2
  where
    mkImpliesWorker impliesFirst impliesSecond impliesSort =
        synthesize (ImpliesF implies')
      where
        implies' = Implies { impliesSort, impliesFirst, impliesSecond }

{- | Construct a 'In' pattern in the given sort.

See also: 'mkIn_'

 -}
mkIn
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn inResultSort t1 t2 = updateCallStack $ makeSortsAgree mkInWorker t1 t2
  where
    mkInWorker inContainedChild inContainingChild inOperandSort =
        synthesize (InF in')
      where
        in' =
            In
                { inOperandSort
                , inResultSort
                , inContainedChild
                , inContainingChild
                }

{- | Construct a 'In' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use 'mkIn'
instead.

See also: 'mkIn'

 -}
mkIn_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn_ t1 t2 = updateCallStack $ mkIn predicateSort t1 t2

{- | Construct a 'Mu' pattern.
 -}
mkMu
    :: HasCallStack
    => InternalVariable variable
    => SetVariable variable
    -> TermLike variable
    -> TermLike variable
mkMu muVar = updateCallStack . makeSortsAgree mkMuWorker (mkSetVar muVar)
  where
    mkMuWorker (SetVar_ muVar') muChild _ =
        synthesize (MuF Mu { muVariable = muVar', muChild })
    mkMuWorker _ _ _ = error "Unreachable code"

{- | Construct a 'Next' pattern.
 -}
mkNext
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
mkNext nextChild =
    updateCallStack $ synthesize (NextF Next { nextSort, nextChild })
  where
    nextSort = termLikeSort nextChild

{- | Construct a 'Not' pattern.
 -}
mkNot
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
mkNot notChild =
    updateCallStack $ synthesize (NotF Not { notSort, notChild })
  where
    notSort = termLikeSort notChild

{- | Construct a 'Nu' pattern.
 -}
mkNu
    :: HasCallStack
    => InternalVariable variable
    => SetVariable variable
    -> TermLike variable
    -> TermLike variable
mkNu nuVar = updateCallStack . makeSortsAgree mkNuWorker (mkSetVar nuVar)
  where
    mkNuWorker (SetVar_ nuVar') nuChild _ =
        synthesize (NuF Nu { nuVariable = nuVar', nuChild })
    mkNuWorker _ _ _ = error "Unreachable code"

{- | Construct an 'Or' pattern.
 -}
mkOr
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkOr t1 t2 = updateCallStack $ makeSortsAgree mkOrWorker t1 t2
  where
    mkOrWorker orFirst orSecond orSort =
        synthesize (OrF Or { orSort, orFirst, orSecond })

{- | Construct a 'Rewrites' pattern.
 -}
mkRewrites
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkRewrites t1 t2 = updateCallStack $ makeSortsAgree mkRewritesWorker t1 t2
  where
    mkRewritesWorker rewritesFirst rewritesSecond rewritesSort =
        synthesize (RewritesF rewrites')
      where
        rewrites' = Rewrites { rewritesSort, rewritesFirst, rewritesSecond }

{- | Construct a 'Top' pattern in the given sort.

See also: 'mkTop_'

 -}
mkTop
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
mkTop topSort =
    updateCallStack $ synthesize (TopF Top { topSort })

{- | Construct a 'Top' pattern in 'predicateSort'.

This should not be used outside "Kore.Internal.Predicate"; please use
'mkTop' instead.

See also: 'mkTop'

 -}
mkTop_
    :: HasCallStack
    => InternalVariable variable
    => TermLike variable
mkTop_ = updateCallStack $ mkTop predicateSort

{- | Construct an element variable pattern.
 -}
mkElemVar
    :: HasCallStack
    => InternalVariable variable
    => ElementVariable variable
    -> TermLike variable
mkElemVar = updateCallStack . mkVar . ElemVar

{- | Construct a set variable pattern.
 -}
mkSetVar
    :: HasCallStack
    => InternalVariable variable
    => SetVariable variable
    -> TermLike variable
mkSetVar = updateCallStack . mkVar . SetVar

{- | Construct a 'StringLiteral' pattern.
 -}
mkStringLiteral
    :: HasCallStack
    => InternalVariable variable
    => Text
    -> TermLike variable
mkStringLiteral =
    updateCallStack . synthesize . StringLiteralF . Const . StringLiteral

mkInternalBytes
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> ByteString
    -> TermLike variable
mkInternalBytes sort value =
    updateCallStack . synthesize . InternalBytesF . Const
        $ InternalBytes
            { bytesSort = sort
            , bytesValue = value
            }

mkInternalBytes'
    :: HasCallStack
    => InternalVariable variable
    => InternalBytes
    -> TermLike variable
mkInternalBytes' = updateCallStack . synthesize . InternalBytesF . Const

mkInhabitant
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
mkInhabitant = updateCallStack . synthesize . InhabitantF . Inhabitant

mkEvaluated
    :: HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkEvaluated = updateCallStack . synthesize . EvaluatedF . Evaluated

{- | Construct an 'Endianness' pattern.
 -}
mkEndianness
    :: HasCallStack
    => Ord variable
    => SortedVariable variable
    => Endianness
    -> TermLike variable
mkEndianness = updateCallStack . synthesize . EndiannessF . Const

{- | Construct an 'Signedness' pattern.
 -}
mkSignedness
    :: HasCallStack
    => Ord variable
    => SortedVariable variable
    => Signedness
    -> TermLike variable
mkSignedness = updateCallStack . synthesize . SignednessF . Const

mkSort :: Id -> Sort
mkSort name = SortActualSort $ SortActual name []

mkSortVariable :: Id -> Sort
mkSortVariable name = SortVariableSort $ SortVariable name

{- | Construct a variable with a given name and sort.

@
"name" `varS` sort
@
 -}
varS :: Id -> Sort -> Variable
varS variableName variableSort =
    Variable
        { variableName
        , variableSort
        , variableCounter = mempty
        }

{- | Construct an element variable with a given name and sort.

@variableName@ should *not* start with the @at@ symbol

@
"name" `elemVarS` sort
@
 -}
elemVarS :: Id -> Sort -> ElementVariable Variable
elemVarS variableName variableSort =
    ElementVariable (varS variableName variableSort)

{- | Construct a set variable with a given name and sort.

@variableName@ should start with the @at@ symbol

@
"name" `setVarS` sort
@
 -}
setVarS :: Id -> Sort -> SetVariable Variable
setVarS variableName variableSort =
    SetVariable (varS variableName variableSort)

{- | Construct an axiom declaration with the given parameters and pattern.
 -}
mkAxiom
    :: [SortVariable]
    -> TermLike variable
    -> SentenceAxiom (TermLike variable)
mkAxiom sentenceAxiomParameters sentenceAxiomPattern =
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes = Attributes []
        }

{- | Construct an axiom declaration with no parameters.

See also: 'mkAxiom'

 -}
mkAxiom_ :: TermLike variable -> SentenceAxiom (TermLike variable)
mkAxiom_ = mkAxiom []

{- | Construct a symbol declaration with the given parameters and sorts.
 -}
mkSymbol
    :: Id
    -> [SortVariable]
    -> [Sort]
    -> Sort
    -> SentenceSymbol (TermLike variable)
mkSymbol symbolConstructor symbolParams argumentSorts resultSort' =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Syntax.Symbol
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
    :: Id
    -> [Sort]
    -> Sort
    -> SentenceSymbol (TermLike variable)
mkSymbol_ symbolConstructor = mkSymbol symbolConstructor []

{- | Construct an alias declaration with the given parameters and sorts.
 -}
mkAlias
    :: Id
    -> [SortVariable]
    -> Sort
    -> [UnifiedVariable Variable]
    -> TermLike Variable
    -> SentenceAlias (TermLike Variable)
mkAlias aliasConstructor aliasParams resultSort' arguments right =
    SentenceAlias
        { sentenceAliasAlias =
            Syntax.Alias
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
    argumentSorts = foldMapVariable variableSort <$> arguments

{- | Construct an alias declaration with no parameters.

See also: 'mkAlias'

 -}
mkAlias_
    :: Id
    -> Sort
    -> [UnifiedVariable Variable]
    -> TermLike Variable
    -> SentenceAlias (TermLike Variable)
mkAlias_ aliasConstructor = mkAlias aliasConstructor []

pattern And_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern App_
    :: Symbol
    -> [TermLike variable]
    -> TermLike variable

pattern ApplyAlias_
    :: Alias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable

pattern Bottom_
    :: Sort
    -> TermLike variable

pattern Ceil_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable

pattern DV_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Builtin_
    :: Domain.Builtin (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinBool_
    :: Domain.InternalBool
    -> TermLike variable

pattern BuiltinInt_
    :: Domain.InternalInt
    -> TermLike variable

pattern BuiltinList_
    :: Domain.InternalList (TermLike variable)
    -> TermLike variable

pattern BuiltinMap_
    :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinSet_
    :: Domain.InternalSet (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinString_
    :: Domain.InternalString
    -> TermLike variable

pattern Equals_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Exists_
    :: Sort
    -> ElementVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Floor_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable

pattern Forall_
    :: Sort
    -> ElementVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Iff_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Implies_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern In_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Mu_
    :: SetVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Next_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Not_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Nu_
    :: SetVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Or_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Rewrites_
  :: Sort
  -> TermLike variable
  -> TermLike variable
  -> TermLike variable

pattern Top_ :: Sort -> TermLike variable

pattern Var_ :: UnifiedVariable variable -> TermLike variable

pattern ElemVar_ :: ElementVariable variable -> TermLike variable

pattern SetVar_ :: SetVariable variable -> TermLike variable

pattern StringLiteral_ :: Text -> TermLike variable

pattern Evaluated_ :: TermLike variable -> TermLike variable

pattern And_ andSort andFirst andSecond <-
    (Recursive.project -> _ :< AndF And { andSort, andFirst, andSecond })

pattern ApplyAlias_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplyAliasF Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )

pattern App_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplySymbolF Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )

pattern Bottom_ bottomSort <-
    (Recursive.project -> _ :< BottomF Bottom { bottomSort })

pattern InternalBytes_ :: Sort -> ByteString -> TermLike variable
pattern InternalBytes_ bytesSort bytesValue <-
    (Recursive.project -> _ :< InternalBytesF (Const InternalBytes
        { bytesSort, bytesValue }
    ))

pattern Ceil_ ceilOperandSort ceilResultSort ceilChild <-
    (Recursive.project ->
        _ :< CeilF Ceil { ceilOperandSort, ceilResultSort, ceilChild }
    )

pattern DV_ domainValueSort domainValueChild <-
    (Recursive.project ->
        _ :< DomainValueF DomainValue { domainValueSort, domainValueChild }
    )

pattern Builtin_ builtin <- (Recursive.project -> _ :< BuiltinF builtin)

pattern BuiltinBool_ internalBool <- Builtin_ (Domain.BuiltinBool internalBool)

pattern BuiltinInt_ internalInt <- Builtin_ (Domain.BuiltinInt internalInt)

pattern BuiltinList_ internalList <- Builtin_ (Domain.BuiltinList internalList)

pattern BuiltinMap_ internalMap <- Builtin_ (Domain.BuiltinMap internalMap)

pattern BuiltinSet_ internalSet <- Builtin_ (Domain.BuiltinSet internalSet)

pattern BuiltinString_ internalString
    <- Builtin_ (Domain.BuiltinString internalString)

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

pattern Mu_ muVariable muChild <-
    (Recursive.project ->
        _ :< MuF Mu { muVariable, muChild }
    )

pattern Next_ nextSort nextChild <-
    (Recursive.project ->
        _ :< NextF Next { nextSort, nextChild })

pattern Not_ notSort notChild <-
    (Recursive.project ->
        _ :< NotF Not { notSort, notChild })

pattern Nu_ nuVariable nuChild <-
    (Recursive.project ->
        _ :< NuF Nu { nuVariable, nuChild }
    )

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
    (Recursive.project -> _ :< VariableF (Const variable))

pattern SetVar_ setVariable <- Var_ (SetVar setVariable)

pattern ElemVar_ elemVariable <- Var_ (ElemVar elemVariable)

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralF (Const (StringLiteral str)))

pattern Evaluated_ child <-
    (Recursive.project -> _ :< EvaluatedF (Evaluated child))

pattern Endianness_ :: Endianness -> TermLike child
pattern Endianness_ endianness <-
    (Recursive.project -> _ :< EndiannessF (Const endianness))

pattern Signedness_ :: Signedness -> TermLike child
pattern Signedness_ signedness <-
    (Recursive.project -> _ :< SignednessF (Const signedness))

pattern Inj_ :: Inj (TermLike child) -> TermLike child
pattern Inj_ inj <- (Recursive.project -> _ :< InjF inj)

refreshBinder
    :: InternalVariable variable
    => (Set (UnifiedVariable variable) -> bound -> Maybe bound)
    -> (bound -> UnifiedVariable variable)
    -> FreeVariables variable
    -> Binder bound (TermLike variable)
    -> Binder bound (TermLike variable)
refreshBinder refreshBound mkUnified (FreeVariables.toSet -> avoiding) binder =
    do
        binderVariable' <- refreshBound avoiding binderVariable
        let renaming =
                Map.singleton
                    (mkUnified binderVariable)
                    (mkVar $ mkUnified binderVariable')
            binderChild' = Substitute.substitute renaming binderChild
        return Binder
            { binderVariable = binderVariable'
            , binderChild = binderChild'
            }
    & fromMaybe binder
  where
    Binder { binderVariable, binderChild } = binder

refreshElementBinder
    :: InternalVariable variable
    => FreeVariables variable
    -> Binder (ElementVariable variable) (TermLike variable)
    -> Binder (ElementVariable variable) (TermLike variable)
refreshElementBinder = refreshBinder refreshElementVariable ElemVar

refreshSetBinder
    :: InternalVariable variable
    => FreeVariables variable
    -> Binder (SetVariable variable) (TermLike variable)
    -> Binder (SetVariable variable) (TermLike variable)
refreshSetBinder = refreshBinder refreshSetVariable SetVar
