{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Substitution
    ( Substitution
    -- Constructor for Assignment not exported
    -- on purpose
    , Assignment
    , assign
    , pattern Assignment
    , assignmentToPair
    , assignedVariable
    , assignedTerm
    , mapAssignedTerm
    , singleSubstitutionToPredicate
    , UnwrappedSubstitution
    , mkUnwrappedSubstitution
    , unwrap
    , toMap
    , toMultiMap
    , normalOrder
    , fromMap
    , singleton
    , wrap
    , modify
    , Kore.Internal.Substitution.mapVariables
    , mapTerms
    , mapAssignmentVariables
    , isNormalized
    , isSimplified
    , forgetSimplified
    , markSimplified
    , simplifiedAttribute
    , null
    , variables
    , unsafeWrap
    , unsafeWrapFromAssignments
    , Kore.Internal.Substitution.filter
    , partition
    , orderRenameAndRenormalizeTODO
    , toPredicate
    , Normalization (..)
    , wrapNormalization
    , mkNormalization
    , applyNormalized
    , substitute
    , orientSubstitution
    ) where

import Prelude.Kore hiding
    ( null
    )

import Control.DeepSeq
    ( NFData
    )
import qualified Data.List as List
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import ErrorContext
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
    ( Unparse
    , unparse
    , unparseToString
    )
import Pretty
    ( Pretty
    )
import qualified Pretty
import qualified SQL

data Assignment variable =
    Assignment_
        { assignedVariable :: !(SomeVariable variable)
        , assignedTerm :: !(TermLike variable)
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance (Ord variable, Unparse variable) => Pretty (Assignment variable) where
    pretty Assignment_ { assignedVariable, assignedTerm } =
        Pretty.vsep
        [ Pretty.hsep ["assigned variable:", unparse assignedVariable]
        , "assigned term:"
        , Pretty.indent 4 (unparse assignedTerm)
        ]

-- | Smart constructor for 'Assignment'. It enforces the invariant
-- that for variable renaming, the smaller variable will be on the
-- left of the substitution.
assign
    :: (Ord variable, SubstitutionOrd variable)
    => SomeVariable variable
    -> TermLike variable
    -> Assignment variable
assign variable term =
    uncurry Assignment_ $ curry normalOrder variable term

pattern Assignment
    :: SomeVariable variable
    -> TermLike variable
    -> Assignment variable
pattern Assignment assignedVariable assignedTerm <-
    Assignment_ { assignedVariable, assignedTerm }
{-# COMPLETE Assignment #-}

assignmentToPair
    :: Assignment variable
    -> (SomeVariable variable, TermLike variable)
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
    :: (Ord variable, SubstitutionOrd variable)
    => [(SomeVariable variable, TermLike variable)]
    -> [Assignment variable]
mkUnwrappedSubstitution = fmap (uncurry assign)

{- | @Substitution@ represents a collection @[xᵢ=φᵢ]@ of substitutions.

Individual substitutions are a pair of type

@
(SomeVariable variable, TermLike variable)
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
        !(Map (SomeVariable variable) (TermLike variable))
    deriving (Show)
    deriving (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

-- | 'Eq' does not differentiate normalized and denormalized 'Substitution's.
instance
    (Ord variable, SubstitutionOrd variable) => Eq (Substitution variable)
  where
    (==) = on (==) unwrap

-- | 'Ord' does not differentiate normalized and denormalized 'Substitution's.
instance
    (Ord variable, SubstitutionOrd variable) => Ord (Substitution variable)
  where
    compare = on compare unwrap

instance
    (Debug variable, Diff variable, Ord variable, SubstitutionOrd variable)
    => Diff (Substitution variable)
  where
    diffPrec a b =
        wrapDiffPrec <$> on diffPrec unwrap a b
      where
        wrapDiffPrec diff' = \precOut ->
            (if precOut >= 10 then Pretty.parens else id)
            ("Kore.Internal.Substitution.wrap" Pretty.<+> diff' 10)

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
    defineColumn tableName _ =
        SQL.defineColumn tableName (SQL.Proxy @(Predicate variable))
    toColumn = SQL.toColumn . toPredicate

instance
    InternalVariable variable =>
    From
        (Map (SomeVariable variable) (TermLike variable))
        (Substitution variable)
  where
    from = wrap . mkUnwrappedSubstitution . Map.toList

instance
    InternalVariable variable
    => From (SomeVariable variable, TermLike variable) (Substitution variable)
  where
    from = uncurry singleton

instance From (UnwrappedSubstitution variable) (Substitution variable) where
    from = wrap

instance
    InternalVariable variable
    => From (Substitution variable) (UnwrappedSubstitution variable)
  where
    from = unwrap

instance From (Assignment variable) (Substitution variable)
  where
    from assignment = wrap [assignment]

instance
    InternalVariable variable
    => From (Assignment variable) (Predicate variable)
  where
    from (Assignment var patt) =
        -- Never mark this as simplified since we want to be able to rebuild the
        -- substitution sometimes (e.g. not(not(subst)) and when simplifying
        -- claims).
        Predicate.makeEqualsPredicate (TermLike.mkVar var) patt

instance
    InternalVariable variable
    => From (Substitution variable) (Predicate variable)
  where
    from =
        Predicate.makeMultipleAndPredicate
        . fmap singleSubstitutionToPredicate
        . unwrap

instance
    InternalVariable variable =>
    From
        (Map (SomeVariableName variable) (TermLike variable))
        (Substitution variable)
  where
    from =
        fromMap . Map.fromAscList . fmap toVariable . Map.toAscList
      where
        toVariable (variableName, term) =
            let variableSort = TermLike.termLikeSort term
             in (Variable { variableName, variableSort }, term)

type UnwrappedSubstitution variable = [Assignment variable]

-- | Unwrap the 'Substitution' to its inner list of substitutions.
unwrap
    :: (Ord variable, SubstitutionOrd variable)
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
    => Ord variable
    => Substitution variable
    -> Map (SomeVariableName variable) (TermLike variable)
toMap (Substitution _) =
    error "Cannot convert a denormalized substitution to a map!"
toMap (NormalizedSubstitution norm) =
    Map.mapKeys variableName norm

toMultiMap
    :: InternalVariable variable
    => Substitution variable
    -> Map (SomeVariable variable) (NonEmpty (TermLike variable))
toMultiMap =
    foldl' insertSubstitution Map.empty
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
        let push = (termLike :|) . maybe [] Prelude.Kore.toList
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
normalOrder
    :: forall variable
    .  (Ord variable, SubstitutionOrd variable)
    => (SomeVariable variable, TermLike variable)
    -> (SomeVariable variable, TermLike variable)
normalOrder (uVar1, Var_ uVar2)
  | Just eVar1 <- retractElementVariable uVar1
  , Just eVar2 <- retractElementVariable uVar2
  , LT <- compareSubstitution eVar2 eVar1
  = (uVar2, mkVar uVar1)

  | Just sVar1 <- retractSetVariable uVar1
  , Just sVar2 <- retractSetVariable uVar2
  , LT <- compareSubstitution sVar2 sVar1
  = (uVar2, mkVar uVar1)
normalOrder subst = subst

fromMap
    :: InternalVariable variable
    => Map (SomeVariable variable) (TermLike variable)
    -> Substitution variable
fromMap = from

{- | Construct substitution for a single variable.

The substitution is normalized if the variable does not occur free in the term.

 -}
singleton
    :: InternalVariable variable
    => SomeVariable variable
    -> TermLike variable
    -> Substitution variable
singleton var@Variable { variableName } termLike
  | TermLike.hasFreeVariable variableName termLike =
      Substitution [assign var termLike]
  | otherwise = NormalizedSubstitution (Map.singleton var termLike)

-- | Wrap the list of substitutions to an un-normalized substitution. Note that
-- @wrap . unwrap@ is not @id@ because the normalization state is lost.
wrap
    :: [Assignment variable]
    -> Substitution variable
wrap [] = NormalizedSubstitution Map.empty
wrap xs = Substitution xs

-- TODO(Ana): change to [Assignment] -> Substitution
-- | Wrap the list of substitutions to a normalized substitution. Do not use
-- this unless you are sure you need it.
unsafeWrap
    :: HasCallStack
    => InternalVariable variable
    => [(SomeVariable variable, TermLike variable)]
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
        -- TODO (thomas.tuegel): isBottom -> isDefinedPattern
        & assert (not $ isElementVariable var && isBottom termLike)
        & withErrorContext "while wrapping substitution" (assign var termLike)
      where
        Variable { variableName } = var
        occurs = TermLike.hasFreeVariable variableName
        depends Variable { variableName = variableName' } =
            TermLike.hasFreeVariable variableName' termLike

unsafeWrapFromAssignments
    :: HasCallStack
    => InternalVariable variable
    => [Assignment variable]
    -> Substitution variable
unsafeWrapFromAssignments =
    unsafeWrap . fmap assignmentToPair

-- | Maps a function over the inner representation of the 'Substitution'. The
-- normalization status is reset to un-normalized.
modify
    :: InternalVariable variable1
    => ( [Assignment variable1] -> [Assignment variable2] )
    -> Substitution variable1
    -> Substitution variable2
modify f = wrap . f . unwrap

mapAssignmentVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> Assignment variable1
    -> Assignment variable2
mapAssignmentVariables adj (Assignment variable term) =
    assign mappedVariable mappedTerm
  where
    mappedVariable = mapSomeVariable adj variable
    mappedTerm = TermLike.mapVariables adj term

-- | 'mapVariables' changes all the variables in the substitution
-- with the given function.
mapVariables
    :: forall variable1 variable2
    .  (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> Substitution variable1
    -> Substitution variable2
mapVariables adj = modify . fmap $ mapAssignmentVariables adj

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

markSimplified
    :: InternalVariable variable
    => Substitution variable -> Substitution variable
markSimplified =
    wrap
    . fmap (mapAssignedTerm TermLike.markSimplified)
    . unwrap

simplifiedAttribute
    :: Substitution variable -> Attribute.Simplified
simplifiedAttribute (Substitution _) = Attribute.NotSimplified
simplifiedAttribute (NormalizedSubstitution normalized) =
    foldMap TermLike.simplifiedAttribute normalized

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
    => (SomeVariable variable -> Bool)
    -> Substitution variable
    -> Substitution variable
filter filtering =
    modify (Prelude.Kore.filter (filtering . assignedVariable))

{- | Return the pair of substitutions that do and do not satisfy the criterion.

The normalization state is preserved.

 -}
partition
    :: (SomeVariable variable -> TermLike variable -> Bool)
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
    => SomeVariable variable
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
                replacementVar :: SomeVariable variable
                replacementVar = foldr max v vs

                replacement :: TermLike variable
                replacement = mkVar replacementVar

                replacedSubstitution
                    :: Map (SomeVariable variable) (TermLike variable)
                replacedSubstitution =
                    fmap
                        (TermLike.substitute
                            (Map.singleton (variableName variable) replacement)
                        )
                        (assertNoneAreFreeVarsInRhs
                            (Set.fromList reversableVars)
                            (Map.delete replacementVar substitution)
                        )
            in
                NormalizedSubstitution
                    (Map.insert variable replacement replacedSubstitution)
  where
    reversable :: [(SomeVariable variable, TermLike variable)]
    reversable = List.filter (rhsIsVar variable) (Map.toList substitution)

    reversableVars :: [SomeVariable variable]
    reversableVars = map fst reversable

    rhsIsVar :: SomeVariable variable -> (thing, TermLike variable) -> Bool
    rhsIsVar var (_, Var_ otherVar) = var == otherVar
    rhsIsVar _ _ = False
orderRenameAndRenormalizeTODO _ substitution = substitution

assertNoneAreFreeVarsInRhs
    :: InternalVariable variable
    => Set (SomeVariable variable)
    -> Map (SomeVariable variable) (TermLike variable)
    -> Map (SomeVariable variable) (TermLike variable)
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
            $ FreeVariables.toSet
            $ freeVariables patt

instance InternalVariable variable
  => HasFreeVariables (Substitution variable) variable
  where
    freeVariables = foldMap freeVariablesWorker . unwrap
      where
        freeVariablesWorker (Assignment x t) =
            freeVariable x <> freeVariables t

-- | The left-hand side variables of the 'Substitution'.
variables
    :: Ord variable
    => Substitution variable
    -> Set (SomeVariable variable)
variables (NormalizedSubstitution subst) = Map.keysSet subst
variables (Substitution subst) =
    foldMap (Set.singleton . assignedVariable) subst

{- | Apply an orientation to all variable-renaming substitutions.

A variable-renaming substitution is a pair of the form

@
X:S = Y:S
@

In a normalized substitution, the variable on the left-hand side of each
substitution pair may not appear in any other substitution pair. The order of a
variable-renaming pair is logically irrelevant, but often we have a preference
for which of @X@ and @Y@ should appear on the left-hand side (that is, we have a
preferred /orientation/).

@orientSubstitution@ applies an orientation to a normalized substitution and
yields a normalized substitution. The orientation is expressed as a function

@
SomeVariableName variable -> Bool
@

returning `True` when the named variable is preferred on the left-hand side of a
variable-renaming substitution pair. Each variable-renaming pair is oriented so
that the variable on the left-hand side is a preferred variable, if possible.
@orientSubstitution@ does not alter substitution pairs where both or neither
variable is preferred for the left-hand side.
-}
orientSubstitution
    :: forall variable
    .  InternalVariable variable
    => (SomeVariableName variable -> Bool)
    -- ^ Orientation: Is the named variable preferred on the left-hand side of
    -- variable-renaming substitution pairs?
    -> Map (SomeVariableName variable) (TermLike variable)
    -- ^ Normalized substitution
    -> Map (SomeVariableName variable) (TermLike variable)
orientSubstitution toLeft substitution =
    foldl' go substitution $ Map.toList substitution
  where
    go substitutionInProgress initialPair@(initialKey, _)
      | Just (newKey, newValue) <- retractReorderedPair initialPair =
        -- Re-orienting X = Y as Y = X.
        let newPair = Map.singleton newKey newValue
        in case Map.lookup newKey substitutionInProgress of
            Nothing ->
                -- There is no other Y = X substitution in the map.
                substitutionInProgress
                -- Remove X = Y pair.
                & Map.delete initialKey
                -- Apply Y = X to the right-hand side of all pairs.
                & Map.map (TermLike.substitute newPair)
                -- Insert Y = X pair.
                & Map.insert newKey newValue
            Just already ->
                -- There is a substitution Y = T in the map.
                substitutionInProgress
                -- Remove Y = T.
                & Map.delete newKey
                -- Apply Y = X to the right-hand side of all pairs.
                & Map.map (TermLike.substitute newPair)
                -- Insert Y = X pair.
                & Map.insert newKey newValue
                -- Apply X = T to the right-hand side of all pairs.
                & Map.map
                    (TermLike.substitute (Map.singleton initialKey already))
                -- Insert X = T pair.
                & Map.insert initialKey already
      | otherwise = substitutionInProgress

    retractReorderedPair
        :: (SomeVariableName variable, TermLike variable)
        -> Maybe (SomeVariableName variable, TermLike variable)
    retractReorderedPair (xName, TermLike.Var_ (Variable yName ySort))
      | isSameMultiplicity xName yName
      , toLeft yName
      , not (toLeft xName)
      = Just (yName, TermLike.mkVar (Variable xName ySort))
    retractReorderedPair _ = Nothing

    isSameMultiplicity
        :: SomeVariableName variable
        -> SomeVariableName variable
        -> Bool
    isSameMultiplicity x y
      | SomeVariableNameElement _ <- x, SomeVariableNameElement _ <- y = True
      | SomeVariableNameSet     _ <- x, SomeVariableNameSet     _ <- y = True
      | otherwise = False

{- | The result of /normalizing/ a substitution.

'normalized' holds the part of the substitution was normalized successfully.

'denormalized' holds the part of the substitution which was not normalized
because it contained simplifiable cycles.

 -}
data Normalization variable =
    Normalization
        { normalized, denormalized :: !(UnwrappedSubstitution variable) }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Semigroup (Normalization variable) where
    (<>) a b =
        Normalization
            { normalized = on (<>) normalized a b
            , denormalized = on (<>) denormalized a b
            }

instance Monoid (Normalization variable) where
    mempty = Normalization mempty mempty

instance InternalVariable variable => Pretty (Normalization variable) where
    pretty Normalization { normalized, denormalized } =
        Pretty.vsep
        [ "normalized:"
        , (Pretty.indent 4 . Pretty.vsep) (map prettyPair normalized)
        , "denormalized:"
        , (Pretty.indent 4 . Pretty.vsep) (map prettyPair denormalized)
        ]
      where
        prettyPair assignment =
            Pretty.vsep
            [ "variable:"
            , Pretty.indent 4 (unparse $ assignedVariable assignment)
            , "term:"
            , Pretty.indent 4 (unparse $ assignedTerm assignment)
            ]

mkNormalization
    :: InternalVariable variable
    => [(SomeVariable variable, TermLike variable)]
    -> [(SomeVariable variable, TermLike variable)]
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
        , denormalized = mapAssignedTerm substitute' <$> denormalized
        }
  where
    substitute' =
        TermLike.substitute
        $ Map.mapKeys variableName
        $ Map.fromList
        $ map assignmentToPair normalized

{- | Apply a 'Map' from names to terms to a substitution.

The given mapping will be applied only to the right-hand sides of the
substitutions (see 'mapAssignedTerm').  The result will not be a normalized
'Substitution'.

 -}
substitute
    :: InternalVariable variable
    => Map (SomeVariableName variable) (TermLike variable)
    -> Substitution variable
    -> Substitution variable
substitute subst =
    wrap . (map . mapAssignedTerm) (TermLike.substitute subst) . unwrap

{- | @toPredicate@ constructs a 'Predicate' equivalent to 'Substitution'.

An empty substitution list returns a true predicate. A non-empty substitution
returns a conjunction of variable-substitution equalities.

-}
toPredicate
    :: InternalVariable variable
    => Substitution variable
    -> Predicate variable
toPredicate = from

singleSubstitutionToPredicate
    :: InternalVariable variable
    => Assignment variable
    -> Predicate variable
singleSubstitutionToPredicate = from
