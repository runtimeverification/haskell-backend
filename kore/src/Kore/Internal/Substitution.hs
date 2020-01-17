{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Substitution
    ( Substitution
    , SingleSubstitution
    , UnwrappedSubstitution
    , unwrap
    , toMap
    , toMultiMap
    , orderRenaming
    , fromMap
    , singleton
    , wrap
    , modify
    , Kore.Internal.Substitution.mapVariables
    , isNormalized
    , simplifiedAttribute
    , null
    , variables
    , unsafeWrap
    , Kore.Internal.Substitution.filter
    , partition
    , reverseIfRhsIsVar
    , toPredicate
    , Normalization (..)
    , wrapNormalization
    , applyNormalized
    ) where

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Exception as Exception
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import Data.Hashable
import qualified Data.List as List
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import GHC.Stack
    ( HasCallStack
    )
import Prelude hiding
    ( null
    )

import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.Simplified as Attribute
    ( Simplified (..)
    )
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( InternalVariable
    , SubstitutionVariable
    , TermLike
    , pattern Var_
    , mkVar
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Variable
    ( SortedVariable
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse
    , unparseToString
    )
import Kore.Variables.Fresh
    ( FreshVariable
    )
import Kore.Variables.UnifiedVariable
import qualified SQL

{- | @Substitution@ represents a collection @[xᵢ=φᵢ]@ of substitutions.

Individual substitutions are a pair of type

@
(UnifiedVariable variable, TermLike variable)
@

A collection of substitutions @[xᵢ=φᵢ]@ is /normalized/ if, for all @xⱼ=φⱼ@ in
the collection, @xⱼ@ is unique among all @xᵢ@ and none of the @xᵢ@ (including
@xⱼ@) occur free in @φⱼ@.

 -}
data Substitution variable
    -- TODO (thomas.tuegel): Instead of a sum type, use a product containing the
    -- normalized and denormalized parts of the substitution together. That
    -- would enable us to keep more substitutions normalized in the Semigroup
    -- instance below.
    = Substitution ![(UnifiedVariable variable, TermLike variable)]
    | NormalizedSubstitution
        !(Map (UnifiedVariable variable) (TermLike variable))
    deriving GHC.Generic

-- | 'Eq' does not differentiate normalized and denormalized 'Substitution's.
instance Ord variable => Eq (Substitution variable) where
    (==) = Function.on (==) unwrap

-- | 'Ord' does not differentiate normalized and denormalized 'Substitution's.
instance Ord variable => Ord (Substitution variable) where
    compare = Function.on compare unwrap

instance SOP.Generic (Substitution variable)

instance SOP.HasDatatypeInfo (Substitution variable)

instance Debug variable => Debug (Substitution variable)

instance
    ( Debug variable, Diff variable, Ord variable )
    => Diff (Substitution variable)
  where
    diffPrec a b =
        wrapDiffPrec <$> Function.on diffPrec unwrap a b
      where
        wrapDiffPrec diff' = \precOut ->
            (if precOut >= 10 then Pretty.parens else id)
            ("Kore.Internal.Substitution.wrap" Pretty.<+> diff' 10)

deriving instance Show variable => Show (Substitution variable)

instance NFData variable => NFData (Substitution variable)

instance Hashable variable => Hashable (Substitution variable) where
    hashWithSalt salt (Substitution denorm) =
        salt `hashWithSalt` (0::Int) `hashWithSalt` denorm
    hashWithSalt salt (NormalizedSubstitution norm) =
        salt `hashWithSalt` (1::Int) `hashWithSalt` Map.toList norm

instance TopBottom (Substitution variable) where
    isTop = null
    isBottom _ = False

instance Ord variable => Semigroup (Substitution variable) where
    a <> b
      | null a, null b = mempty
      | null a         = b
      | null b         = a
      | otherwise      = Substitution (unwrap a <> unwrap b)

instance Ord variable => Monoid (Substitution variable) where
    mempty = NormalizedSubstitution mempty

instance InternalVariable variable => SQL.Column (Substitution variable) where
    defineColumn _ = SQL.defineColumn (Proxy @(Predicate variable))
    toColumn = SQL.toColumn . toPredicate

type SingleSubstitution variable = (UnifiedVariable variable, TermLike variable)

type UnwrappedSubstitution variable = [SingleSubstitution variable]

-- | Unwrap the 'Substitution' to its inner list of substitutions.
unwrap
    :: Ord variable
    => Substitution variable
    -> [(UnifiedVariable variable, TermLike variable)]
unwrap (Substitution xs) = List.sortBy (Function.on compare fst) xs
unwrap (NormalizedSubstitution xs)  = Map.toList xs

{- | Convert a normalized substitution to a 'Map'.

@toMap@ throws an error if the substitution is not normalized because the
conversion to a @Map@ would be unsound.

See also: 'fromMap'

 -}
toMap
    :: HasCallStack
    => Substitution variable
    -> Map (UnifiedVariable variable) (TermLike variable)
toMap (Substitution _) =
    error "Cannot convert a denormalized substitution to a map!"
toMap (NormalizedSubstitution norm) = norm

toMultiMap
    :: InternalVariable variable
    => Substitution variable
    -> Map (UnifiedVariable variable) (NonEmpty (TermLike variable))
toMultiMap =
    Foldable.foldl' insertSubstitution Map.empty
    . map orderRenaming
    . unwrap
  where
    insertSubstitution
        :: forall variable1 term
        .  Ord variable1
        => Map variable1 (NonEmpty term)
        -> (variable1, term)
        -> Map variable1 (NonEmpty term)
    insertSubstitution multiMap (variable, termLike) =
        let push = (termLike :|) . maybe [] Foldable.toList
        in Map.alter (Just . push) variable multiMap

{- | Apply a normal order to variable-renaming substitutions.

A variable-renaming substitution has one of the forms,

@
x:S{} = y:S{}
\@X:S{} = \@Y:S{}
@

These are __not__ variable-renaming substitutions because they change variable
types:

@
x:S{} = \@Y:S{}
\@X:S{} = y:S{}
@

Variable-renaming substitutions are sorted so that the greater variable is
substituted in place of the lesser. Consistent ordering prevents variable-only
cycles.

 -}
orderRenaming
    :: InternalVariable variable
    => (UnifiedVariable variable, TermLike variable)
    -> (UnifiedVariable variable, TermLike variable)
orderRenaming (uVar1, Var_ uVar2)
  | ElemVar eVar1 <- uVar1
  , ElemVar eVar2 <- uVar2
  , eVar2 < eVar1 = (uVar2, mkVar uVar1)

  | SetVar sVar1 <- uVar1
  , SetVar sVar2 <- uVar2
  , sVar2 < sVar1 = (uVar2, mkVar uVar1)
orderRenaming subst = subst

fromMap
    :: Map (UnifiedVariable variable) (TermLike variable)
    -> Substitution variable
fromMap = wrap . Map.toList

{- | Construct substitution for a single variable.

The substitution is normalized if the variable does not occur free in the term.

 -}
singleton
    :: Ord variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Substitution variable
singleton var termLike
  | TermLike.hasFreeVariable var termLike = Substitution [(var, termLike)]
  | otherwise = NormalizedSubstitution (Map.singleton var termLike)

-- | Wrap the list of substitutions to an un-normalized substitution. Note that
-- @wrap . unwrap@ is not @id@ because the normalization state is lost.
wrap
    :: [(UnifiedVariable variable, TermLike variable)]
    -> Substitution variable
wrap [] = NormalizedSubstitution Map.empty
wrap xs = Substitution xs

-- | Wrap the list of substitutions to a normalized substitution. Do not use
-- this unless you are sure you need it.
unsafeWrap
    :: Ord variable
    => [(UnifiedVariable variable, TermLike variable)]
    -> Substitution variable
unsafeWrap =
    NormalizedSubstitution . List.foldl' insertNormalized Map.empty
  where
    insertNormalized subst (var, termLike) =
        -- The variable must not occur in the substitution
        Exception.assert (Map.notMember var subst)
        -- or in the right-hand side of this or any other substitution,
        $ Exception.assert (not $ occurs termLike)
        $ Exception.assert (not $ any occurs subst)
        -- this substitution must not depend on any substitution variable,
        $ Exception.assert (not $ any depends $ Map.keys subst)
        -- and if this is an element variable substitution, the substitution
        -- must be defined.
        $ Exception.assert (not $ isElemVar var && isBottom termLike)
        $ Map.insert var termLike subst
      where
        occurs = TermLike.hasFreeVariable var
        depends var' = TermLike.hasFreeVariable var' termLike

-- | Maps a function over the inner representation of the 'Substitution'. The
-- normalization status is reset to un-normalized.
modify
    :: Ord variable1
    => ([(UnifiedVariable variable1, TermLike variable1)]
            -> [(UnifiedVariable variable2, TermLike variable2)])
    -> Substitution variable1
    -> Substitution variable2
modify f = wrap . f . unwrap

-- | 'mapVariables' changes all the variables in the substitution
-- with the given function.
mapVariables
    :: forall variableFrom variableTo
    .  (Ord variableFrom, Ord variableTo)
    => (variableFrom -> variableTo)
    -> Substitution variableFrom
    -> Substitution variableTo
mapVariables variableMapper =
    modify (map (mapVariable variableMapper))
  where
    mapVariable
        :: (variableFrom -> variableTo)
        -> (UnifiedVariable variableFrom, TermLike variableFrom)
        -> (UnifiedVariable variableTo, TermLike variableTo)
    mapVariable
        mapper
        (substVariable, patt)
      =
        (mapper <$> substVariable, TermLike.mapVariables mapper patt)

-- | Returns true iff the substitution is normalized.
isNormalized :: Substitution variable -> Bool
isNormalized (Substitution _)           = False
isNormalized (NormalizedSubstitution _) = True

simplifiedAttribute
    :: Substitution variable -> Attribute.Simplified
simplifiedAttribute (Substitution _) = Attribute.NotSimplified
simplifiedAttribute (NormalizedSubstitution normalized) =
    Foldable.foldMap TermLike.simplifiedAttribute normalized

-- | Returns true iff the substitution is empty.
null :: Substitution variable -> Bool
null (Substitution denorm)         = List.null denorm
null (NormalizedSubstitution norm) = Map.null norm

-- | Filter the variables of the 'Substitution'.
filter
    :: Ord variable
    => (UnifiedVariable variable -> Bool)
    -> Substitution variable
    -> Substitution variable
filter filtering =
    modify (Prelude.filter (filtering . fst))

{- | Return the pair of substitutions that do and do not satisfy the criterion.

The normalization state is preserved.

 -}
partition
    :: (UnifiedVariable variable -> TermLike variable -> Bool)
    -> Substitution variable
    -> (Substitution variable, Substitution variable)
partition criterion (Substitution substitution) =
    let (true, false) = List.partition (uncurry criterion) substitution
    in (Substitution true, Substitution false)
partition criterion (NormalizedSubstitution substitution) =
    let (true, false) = Map.partitionWithKey criterion substitution
    in (NormalizedSubstitution true, NormalizedSubstitution false)

{- | Reverses all `var = givenVar` assignments in the substitution and
renormalizes, if needed.
-}
reverseIfRhsIsVar
    :: forall variable
    .   ( InternalVariable variable
        , FreshVariable variable
        )
    => UnifiedVariable variable
    -> Substitution variable
    -> Substitution variable
reverseIfRhsIsVar variable (Substitution substitution) =
    Substitution (map (reversePairIfRhsVar variable) substitution)
  where
    reversePairIfRhsVar
        :: UnifiedVariable variable
        -> (UnifiedVariable variable, TermLike variable)
        -> (UnifiedVariable variable, TermLike variable)
    reversePairIfRhsVar var (substVar, Var_ substitutionVar)
      | var == substitutionVar =
          (substitutionVar, mkVar substVar)
    reversePairIfRhsVar _ original = original
reverseIfRhsIsVar variable original@(NormalizedSubstitution substitution) =
    case reversableVars of
        [] -> original
        (v:vs) ->
            let
                replacementVar :: UnifiedVariable variable
                replacementVar = foldr max v vs

                replacement :: TermLike variable
                replacement = mkVar replacementVar

                replacedSubstitution
                    :: Map (UnifiedVariable variable) (TermLike variable)
                replacedSubstitution =
                    fmap
                        (TermLike.substitute
                            (Map.singleton variable replacement)
                        )
                        (assertNoneAreFreeVarsInRhs
                            (Set.fromList reversableVars)
                            (Map.delete replacementVar substitution)
                        )
            in
                NormalizedSubstitution
                    (Map.insert variable replacement replacedSubstitution)
  where
    reversable :: [(UnifiedVariable variable, TermLike variable)]
    reversable = List.filter (rhsIsVar variable) (Map.toList substitution)

    reversableVars :: [UnifiedVariable variable]
    reversableVars = map fst reversable

    rhsIsVar :: UnifiedVariable variable -> (thing, TermLike variable) -> Bool
    rhsIsVar var (_, Var_ otherVar) = var == otherVar
    rhsIsVar _ _ = False

assertNoneAreFreeVarsInRhs
    ::  ( Ord variable
        , SortedVariable variable
        , Unparse variable
        )
    => Set (UnifiedVariable variable)
    -> Map (UnifiedVariable variable) (TermLike variable)
    -> Map (UnifiedVariable variable) (TermLike variable)
assertNoneAreFreeVarsInRhs lhsVariables =
    fmap assertNoneAreFree
  where
    assertNoneAreFree patt =
        if Set.null commonVars
        then patt
        else (error . unlines)
            [ "Unexpected lhs variable in rhs term "
            , "in normalized substitution. While this can"
            , "be a valid case sometimes, i.e. x=f(x),"
            , "we don't handle that right now."
            , "patt=" ++ unparseToString patt
            , "commonVars="
                ++ show
                    ( unparseToString
                    <$> Set.toList commonVars
                    )
            ]
      where
        commonVars =
            Set.intersection lhsVariables
            $ getFreeVariables
            $ freeVariables patt

instance Ord variable => HasFreeVariables (Substitution variable) variable
  where
    freeVariables = Foldable.foldMap freeVariablesWorker . unwrap
      where
        freeVariablesWorker (x, t) =
            freeVariable x <> freeVariables t

-- | The left-hand side variables of the 'Substitution'.
variables
    :: Ord variable
    => Substitution variable
    -> Set (UnifiedVariable variable)
variables (NormalizedSubstitution subst) = Map.keysSet subst
variables (Substitution subst) = Foldable.foldMap (Set.singleton . fst) subst

{- | The result of /normalizing/ a substitution.

'normalized' holds the part of the substitution was normalized successfully.

'denormalized' holds the part of the substitution which was not normalized
because it contained simplifiable cycles.

 -}
data Normalization variable =
    Normalization
        { normalized, denormalized :: !(UnwrappedSubstitution variable) }
    deriving (Eq, Ord, Show)
    deriving GHC.Generic

instance SOP.Generic (Normalization variable)

instance SOP.HasDatatypeInfo (Normalization variable)

instance Debug variable => Debug (Normalization variable)

instance (Debug variable, Diff variable) => Diff (Normalization variable)

instance Semigroup (Normalization variable) where
    (<>) a b =
        Normalization
            { normalized = Function.on (<>) normalized a b
            , denormalized = Function.on (<>) denormalized a b
            }

instance Monoid (Normalization variable) where
    mempty = Normalization mempty mempty

wrapNormalization :: Normalization variable -> Substitution variable
wrapNormalization Normalization { normalized, denormalized } =
    wrap (normalized <> denormalized)

-- | Substitute the 'normalized' part into the 'denormalized' part.
applyNormalized
    :: SubstitutionVariable variable
    => Normalization variable
    -> Normalization variable
applyNormalized Normalization { normalized, denormalized } =
    Normalization
        { normalized
        , denormalized = (fmap . fmap) substitute denormalized
        }
  where
    substitute = TermLike.substitute (Map.fromList normalized)

{- | @toPredicate@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
toPredicate
    :: InternalVariable variable
    => Substitution variable
    -> Predicate variable
toPredicate =
    Predicate.makeMultipleAndPredicate
    . fmap Predicate.singleSubstitutionToPredicate
    . unwrap
