{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Substitution
    ( Substitution
    , Assignment
    , assign
    , pattern Assignment_
    , assignmentToPair
    , assignedVariable
    , assignedTerm
    , mapAssignedTerm
    , UnwrappedSubstitution
    , mkUnwrappedSubstitution
    , unwrap
    , toMap
    , toMultiMap
    , orderRenaming
    , fromMap
    , singleton
    , wrap
    , modify
    , Kore.Internal.Substitution.mapVariables
    , mapTerms
    , isNormalized
    , isSimplified
    , forgetSimplified
    , simplifiedAttribute
    , null
    , variables
    , unsafeWrap
    , Kore.Internal.Substitution.filter
    , partition
    , orderRenameAndRenormalizeTODO
    , toPredicate
    , Normalization (..)
    , wrapNormalization
    , mkNormalization
    , applyNormalized
    ) where

import Prelude.Kore hiding
    ( null
    )

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Foldable as Foldable
import Data.Hashable
import qualified Data.List as List
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.Simplified as Attribute
    ( Simplified (..)
    )
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike
    ( TermLike
    , pattern Var_
    , mkVar
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( unparseToString
    )
import Kore.Variables.UnifiedVariable
import qualified SQL

data Assignment variable =
    Assignment
        { assignedVariable :: !(UnifiedVariable variable)
        , assignedTerm :: !(TermLike variable)
        }
    deriving (Show, Eq, Ord, GHC.Generic)

instance SOP.Generic (Assignment variable)

instance SOP.HasDatatypeInfo (Assignment variable)

instance Debug variable => Debug (Assignment variable)

instance
    ( Debug variable, Diff variable, Ord variable )
    => Diff (Assignment variable)

instance NFData variable => NFData (Assignment variable)

instance Hashable variable => Hashable (Assignment variable)

assign
    :: InternalVariable variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Assignment variable
assign variable term =
    uncurry Assignment $ curry orderRenaming variable term

-- TODO: docs
pattern Assignment_
    :: UnifiedVariable variable
    -> TermLike variable
    -> Assignment variable
pattern Assignment_ variable term <-
    Assignment variable term

assignmentToPair
    :: Assignment variable
    -> (UnifiedVariable variable, TermLike variable)
assignmentToPair (Assignment variable term) =
    (variable, term)

mapAssignedTerm
    :: InternalVariable variable
    => (TermLike variable -> TermLike variable)
    -> Assignment variable
    -> Assignment variable
mapAssignedTerm f (Assignment variable term) =
    assign variable (f term)

mkUnwrappedSubstitution
    :: InternalVariable variable
    => [(UnifiedVariable variable, TermLike variable)]
    -> [Assignment variable]
mkUnwrappedSubstitution = fmap (uncurry assign)

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
    = Substitution ![Assignment variable]
    | NormalizedSubstitution
        !(Map (UnifiedVariable variable) (TermLike variable))
    deriving GHC.Generic

-- | 'Eq' does not differentiate normalized and denormalized 'Substitution's.
instance InternalVariable variable => Eq (Substitution variable) where
    (==) = on (==) unwrap

-- | 'Ord' does not differentiate normalized and denormalized 'Substitution's.
instance InternalVariable variable => Ord (Substitution variable) where
    compare = on compare unwrap

instance SOP.Generic (Substitution variable)

instance SOP.HasDatatypeInfo (Substitution variable)

instance Debug variable => Debug (Substitution variable)

instance (InternalVariable variable, Diff variable)
    => Diff (Substitution variable)
  where
    diffPrec a b =
        wrapDiffPrec <$> on diffPrec unwrap a b
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

instance InternalVariable variable => Semigroup (Substitution variable) where
    a <> b
      | null a, null b = mempty
      | null a         = b
      | null b         = a
      | otherwise      = Substitution (unwrap a <> unwrap b)

instance InternalVariable variable => Monoid (Substitution variable) where
    mempty = NormalizedSubstitution mempty

instance InternalVariable variable => SQL.Column (Substitution variable) where
    defineColumn _ = SQL.defineColumn (SQL.Proxy @(Predicate variable))
    toColumn = SQL.toColumn . toPredicate

instance
    InternalVariable variable =>
    From
        (Map (UnifiedVariable variable) (TermLike variable))
        (Substitution variable)
  where
    from = wrap . mkUnwrappedSubstitution . Map.toList

instance
    InternalVariable variable
    => From (UnifiedVariable variable, TermLike variable) (Substitution variable)
  where
    from = uncurry singleton

instance From (UnwrappedSubstitution variable) (Substitution variable) where
    from = wrap

instance
    InternalVariable variable
    => From (Substitution variable) (UnwrappedSubstitution variable)
  where
    from = unwrap

instance
    InternalVariable variable
    => From (Substitution variable) (Predicate variable)
  where
    from =
        Predicate.makeMultipleAndPredicate
        . fmap Predicate.singleSubstitutionToPredicate
        . fmap assignmentToPair
        . unwrap

type UnwrappedSubstitution variable = [Assignment variable]

-- | Unwrap the 'Substitution' to its inner list of substitutions.
unwrap
    :: InternalVariable variable
    => Substitution variable
    -> [Assignment variable]
unwrap (Substitution xs) =
    List.sortBy (on compare assignedVariable) xs
unwrap (NormalizedSubstitution xs) =
    mkUnwrappedSubstitution $ Map.toList xs

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
    . fmap assignmentToPair
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

{- | Apply a normal order to a single substitution.

In practice, this means sorting variable-renaming substitutions.
A variable-renaming substitution is one of the forms,

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
  , LT <- compareSubstitution eVar2 eVar1
  = (uVar2, mkVar uVar1)

  | SetVar sVar1 <- uVar1
  , SetVar sVar2 <- uVar2
  , LT <- compareSubstitution sVar2 sVar1
  = (uVar2, mkVar uVar1)
orderRenaming subst = subst

fromMap
    :: InternalVariable variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Substitution variable
fromMap = from

{- | Construct substitution for a single variable.

The substitution is normalized if the variable does not occur free in the term.

 -}
singleton
    :: InternalVariable variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Substitution variable
singleton var termLike
  | TermLike.hasFreeVariable var termLike =
      Substitution [assign var termLike]
  | otherwise = NormalizedSubstitution (Map.singleton var termLike)

-- | Wrap the list of substitutions to an un-normalized substitution. Note that
-- @wrap . unwrap@ is not @id@ because the normalization state is lost.
wrap
    :: [Assignment variable]
    -> Substitution variable
wrap [] = NormalizedSubstitution Map.empty
wrap xs = Substitution xs

-- | Wrap the list of substitutions to a normalized substitution. Do not use
-- this unless you are sure you need it.
-- TODO: change type to [Assignment] -> Substitution
unsafeWrap
    :: HasCallStack
    => Ord variable
    => [(UnifiedVariable variable, TermLike variable)]
    -> Substitution variable
unsafeWrap =
    NormalizedSubstitution . List.foldl' insertNormalized Map.empty
  where
    insertNormalized subst (var, termLike) =
        Map.insert var termLike subst
        -- The variable must not occur in the substitution
        & assert (Map.notMember var subst)
        -- or in the right-hand side of this or any other substitution,
        & assert (not $ occurs termLike)
        & assert (not $ any occurs subst)
        -- this substitution must not depend on any substitution variable,
        & assert (not $ any depends $ Map.keys subst)
        -- and if this is an element variable substitution, the substitution
        -- must be defined.
        & assert (not $ isElemVar var && isBottom termLike)
      where
        occurs = TermLike.hasFreeVariable var
        depends var' = TermLike.hasFreeVariable var' termLike

-- | Maps a function over the inner representation of the 'Substitution'. The
-- normalization status is reset to un-normalized.
modify
    :: InternalVariable variable1
    => ( [Assignment variable1]
       -> [Assignment variable2]
       )
    -> Substitution variable1
    -> Substitution variable2
modify f = wrap . f . unwrap

mapAssignmentVariables
    :: (InternalVariable variableFrom, InternalVariable variableTo)
    => (ElementVariable variableFrom -> ElementVariable variableTo)
    -> (SetVariable variableFrom -> SetVariable variableTo)
    -> Assignment variableFrom
    -> Assignment variableTo
mapAssignmentVariables mapElemVar mapSetVar (Assignment variable term) =
    assign mappedVariable mappedTerm
  where
    mappedVariable = mapUnifiedVariable mapElemVar mapSetVar variable
    mappedTerm = TermLike.mapVariables mapElemVar mapSetVar term

-- | 'mapVariables' changes all the variables in the substitution
-- with the given function.
mapVariables
    :: forall variableFrom variableTo
    .  (InternalVariable variableFrom, InternalVariable variableTo)
    => (ElementVariable variableFrom -> ElementVariable variableTo)
    -> (SetVariable variableFrom -> SetVariable variableTo)
    -> Substitution variableFrom
    -> Substitution variableTo
mapVariables mapElemVar mapSetVar  =
    modify . fmap
    $ mapAssignmentVariables mapElemVar mapSetVar

mapTerms
    :: InternalVariable variable
    => (TermLike variable -> TermLike variable)
    -> Substitution variable -> Substitution variable
mapTerms mapper (Substitution s) =
    Substitution (mapAssignedTerm mapper <$> s)
mapTerms mapper (NormalizedSubstitution s) =
    NormalizedSubstitution (fmap mapper s)

isSimplified :: SideCondition.Representation -> Substitution variable -> Bool
isSimplified _ (Substitution _) = False
isSimplified sideCondition (NormalizedSubstitution normalized) =
    all (TermLike.isSimplified sideCondition) normalized

forgetSimplified
    :: InternalVariable variable
    => Substitution variable -> Substitution variable
forgetSimplified =
    wrap
    . fmap (mapAssignedTerm TermLike.forgetSimplified)
    . unwrap

simplifiedAttribute
    :: Substitution variable -> Attribute.Simplified
simplifiedAttribute (Substitution _) = Attribute.NotSimplified
simplifiedAttribute (NormalizedSubstitution normalized) =
    Foldable.foldMap TermLike.simplifiedAttribute normalized

-- | Returns true iff the substitution is normalized.
isNormalized :: Substitution variable -> Bool
isNormalized (Substitution _)           = False
isNormalized (NormalizedSubstitution _) = True

-- | Returns true iff the substitution is empty.
null :: Substitution variable -> Bool
null (Substitution denorm)         = List.null denorm
null (NormalizedSubstitution norm) = Map.null norm

-- | Filter the variables of the 'Substitution'.
filter
    :: InternalVariable variable
    => (UnifiedVariable variable -> Bool)
    -> Substitution variable
    -> Substitution variable
filter filtering =
    modify (Prelude.Kore.filter (filtering . assignedVariable))

{- | Return the pair of substitutions that do and do not satisfy the criterion.

The normalization state is preserved.

 -}
partition
    :: (UnifiedVariable variable -> TermLike variable -> Bool)
    -> Substitution variable
    -> (Substitution variable, Substitution variable)
partition criterion (Substitution substitution) =
    let (true, false) =
            List.partition
                (uncurry criterion . assignmentToPair)
                substitution
    in (Substitution true, Substitution false)
partition criterion (NormalizedSubstitution substitution) =
    let (true, false) = Map.partitionWithKey criterion substitution
    in (NormalizedSubstitution true, NormalizedSubstitution false)

-- TODO(Ana): this will be refactored in a subsequent PR
orderRenameAndRenormalizeTODO
    :: forall variable
    .  InternalVariable variable
    => UnifiedVariable variable
    -> Substitution variable
    -> Substitution variable
orderRenameAndRenormalizeTODO
    variable
    original@(NormalizedSubstitution substitution)
  =
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
orderRenameAndRenormalizeTODO _ substitution = substitution

assertNoneAreFreeVarsInRhs
    :: InternalVariable variable
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

instance InternalVariable variable
  => HasFreeVariables (Substitution variable) variable
  where
    freeVariables = Foldable.foldMap freeVariablesWorker . unwrap
      where
        freeVariablesWorker (Assignment x t) =
            freeVariable x <> freeVariables t

-- | The left-hand side variables of the 'Substitution'.
variables
    :: Ord variable
    => Substitution variable
    -> Set (UnifiedVariable variable)
variables (NormalizedSubstitution subst) = Map.keysSet subst
variables (Substitution subst) =
    Foldable.foldMap (Set.singleton . assignedVariable) subst

{- | The result of /normalizing/ a substitution.

'normalized' holds the part of the substitution was normalized successfully.

'denormalized' holds the part of the substitution which was not normalized
because it contained simplifiable cycles.

 -}
data Normalization variable =
    Normalization
        { normalized, denormalized :: !(UnwrappedSubstitution variable) }
    deriving (Eq, Ord, Show, GHC.Generic)

instance SOP.Generic (Normalization variable)

instance SOP.HasDatatypeInfo (Normalization variable)

instance Debug variable => Debug (Normalization variable)

instance (Ord variable, Debug variable, Diff variable) => Diff (Normalization variable)

instance Semigroup (Normalization variable) where
    (<>) a b =
        Normalization
            { normalized = on (<>) normalized a b
            , denormalized = on (<>) denormalized a b
            }

instance Monoid (Normalization variable) where
    mempty = Normalization mempty mempty

mkNormalization
    :: InternalVariable variable
    => [(UnifiedVariable variable, TermLike variable)]
    -> [(UnifiedVariable variable, TermLike variable)]
    -> Normalization variable
mkNormalization normalized' denormalized' =
    Normalization
        (mkUnwrappedSubstitution normalized')
        (mkUnwrappedSubstitution denormalized')

wrapNormalization :: Normalization variable -> Substitution variable
wrapNormalization Normalization { normalized, denormalized } =
    wrap (normalized <> denormalized)

-- | Substitute the 'normalized' part into the 'denormalized' part.
applyNormalized
    :: InternalVariable variable
    => Normalization variable
    -> Normalization variable
applyNormalized Normalization { normalized, denormalized } =
    Normalization
        { normalized
        , denormalized =
            mapAssignedTerm substitute <$> denormalized
        }
  where
    substitute =
        TermLike.substitute
            (Map.fromList (assignmentToPair <$> normalized))

{- | @toPredicate@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
toPredicate
    :: InternalVariable variable
    => Substitution variable
    -> Predicate variable
toPredicate = from
