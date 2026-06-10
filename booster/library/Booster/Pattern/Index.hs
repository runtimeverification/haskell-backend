{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Everything to do with term indexing.
-}
module Booster.Pattern.Index (
    CellIndex (..),
    TermIndex (..),
    -- Flat lattice
    (^<=^),
    invert,
    -- compute index cover for rule selection
    covering,
    -- indexing
    compositeTermIndex,
    kCellTermIndex,
    termTopIndex,
    -- equation indexing (depth-1)
    EquationTheory (..),
    equationLhsIndex,
    equationSubjectIndex,
    -- helpers
    hasNone,
    noFunctions,
) where

import Control.Applicative (Alternative (..), asum)
import Control.DeepSeq (NFData)
import Data.ByteString.Char8 (ByteString, unpack)
import Data.Functor.Foldable (embed, para)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Prettyprinter (Doc, Pretty, pretty, sep)

import Booster.Pattern.Base
import Booster.Util (decodeLabel)

{- | Index data allowing for a quick lookup of potential axioms.

A @Term@ is indexed by inspecting the top term component of one or
more given cells. A @TermIndex@ is a list of @CellIndex@es.

The @CellIndex@ of a cell reflects the top constructor of the term.
For @SymbolApplication@s, constructors and functions are distinguished,
for @DomainValue@s, the actual value (as a string) is part of the index.
Internalised collections have special indexes, Variables have index @Anything@.

NB Indexes are _unsorted_. For instance, @IdxVal "42"@ is the index of
both String "42" _and_ Integer 42.

Rather than making the term indexing function partial, we introduce a
unique bottom element @IdxNone@ to the index type (to make it a lattice).
This can then handle @AndTerm@ by indexing both arguments and
combining them.

NB for technical reasons we derive 'Ord' instances but it does not
reflect the fact that different symbols (and likewise different
constructors) are incompatible (partial ordering).
-}
newtype TermIndex = TermIndex [CellIndex]
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data CellIndex
    = IdxNone -- bottom element
    | IdxCons SymbolName
    | IdxFun SymbolName
    | IdxVal ByteString
    | -- | bare variable in a _subject_ argument position (only produced
      -- by 'equationSubjectIndex' for simplification lookup): a bare
      -- variable can never syntactically /match/ a non-variable pattern,
      -- so only @Anything@ pattern components cover it. Rule-side
      -- indexes never contain it.
      IdxVar
    | IdxMap
    | IdxList
    | IdxSet
    | Anything -- top element
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

{- | Index lattice class. This is mostly just a _flat lattice_ but also
  needs to support a special 'invert' method for the subject term index.
-}
class IndexLattice a where
    (^<=^) :: a -> a -> Bool

    invert :: a -> a

{- | Partial less-or-equal for CellIndex (implies partial order)

                Anything
   ____________/    |  \_______________________________________...
  /          /      |           |           \             \
IdxList ..IdxSet   IdxVal "x"..IdxVal "y"  IdxCons "A"..  IdxFun "f"..
  \_________|__     |    _______|____________|____________/____...
                \   |   /
                 IdxNone
-}
instance IndexLattice CellIndex where
    IdxNone ^<=^ _ = True
    a ^<=^ IdxNone = a == IdxNone
    _ ^<=^ Anything = True
    Anything ^<=^ a = a == Anything
    a ^<=^ b = a == b

    invert IdxNone = Anything
    invert Anything = IdxNone
    invert a = a

-- | Partial less-or-equal for TermIndex (product lattice)
instance IndexLattice TermIndex where
    TermIndex idxs1 ^<=^ TermIndex idxs2 = and $ zipWith (^<=^) idxs1 idxs2

    invert (TermIndex idxs) = TermIndex (map invert idxs)

{- | Combines two indexes ("infimum" or "meet" function on the index lattice).

  This is useful for terms containing an 'AndTerm': Any term that
  matches an 'AndTerm t1 t2' must match both 't1' and 't2', so 't1'
  and 't2' must have "compatible" indexes for this to be possible.
-}
instance Semigroup CellIndex where
    IdxNone <> _ = IdxNone
    _ <> IdxNone = IdxNone
    x <> Anything = x
    Anything <> x = x
    idx1 <> idx2
        | idx1 == idx2 = idx1
        | otherwise = IdxNone

-- | Pretty instances
instance Pretty TermIndex where
    pretty (TermIndex ixs) = sep $ map pretty ixs

instance Pretty CellIndex where
    pretty IdxNone = "_|_"
    pretty Anything = "***"
    pretty (IdxCons sym) = "C--" <> prettyLabel sym
    pretty (IdxFun sym) = "F--" <> prettyLabel sym
    pretty (IdxVal sym) = "V--" <> prettyLabel sym
    pretty IdxVar = "Var"
    pretty IdxMap = "Map"
    pretty IdxList = "List"
    pretty IdxSet = "Set"

prettyLabel :: ByteString -> Doc a
prettyLabel = either error (pretty . unpack) . decodeLabel

{- | Check whether a @TermIndex@ has @IdxNone@ in any position (this
means no match will be possible).
-}
hasNone :: TermIndex -> Bool
hasNone (TermIndex ixs) = IdxNone `elem` ixs

-- | turns IdxFun _ into Anything (for rewrite rule selection)
noFunctions :: TermIndex -> TermIndex
noFunctions (TermIndex ixs) = TermIndex (map funsAnything ixs)
  where
    funsAnything IdxFun{} = Anything
    funsAnything other = other

{- | Computes all indexes that "cover" the given index, for rule lookup.

  An index B is said to "cover" an index A if all components of B are
  greater or equal to those of the respective component of A inverted.

  * For components of A that are distinct from @Anything@, this means
    the component of B is equal to that of A or @Anything@.
  * For components of A that are @IdxNone@, the respective component of B
    _must_ be @Anything@. However, if A contains @IdxNone@ no match is
    possible anyway.
  * For components of A that are @Anything@, B can contain an
    arbitrary index (@IdxNone@ will again have no chance of a match,
    though).

  When selecting candidate rules for a term, we must consider all
  rules whose index has either the exact same @CellIndex@ or
  @Anything@ at every position of their @TermIndex@.
-}
covering :: Set TermIndex -> TermIndex -> Set TermIndex
covering prior ix = Set.filter (invert ix ^<=^) prior

-- | Indexes a term by the heads of K sequences in given cells.
compositeTermIndex :: [SymbolName] -> Term -> TermIndex
compositeTermIndex cells t = TermIndex [kCellIndexFor c t | c <- cells]

-- | Indexes a term by the head of its <k>-cell.
kCellTermIndex :: Term -> TermIndex
kCellTermIndex config = TermIndex [kCellIndexFor "Lbl'-LT-'k'-GT-'" config]

{- | Indexes a term by the head of a K sequence inside a given cell
   (supplied name should have prefix "Lbl'-LT-'" and suffix "'-GT-'").

   Returns either the cell index of the head of the K sequence, or the
   cell index of '.dotk' if the K sequence was empty.
-}
kCellIndexFor :: SymbolName -> Term -> CellIndex
kCellIndexFor name config = fromMaybe Anything $ do
    inCell <- getCell name config
    cellArg1 <- firstArgument inCell
    seqHead <- getKSeqHead cellArg1
    pure $ cellTopIndex seqHead
  where
    firstArgument :: Term -> Maybe Term
    firstArgument = \case
        SymbolApplication _ _ (x : _) -> Just x
        _otherwise -> Nothing --

{- | Retrieve the cell contents of the cell with the given name.
   It is assumed there is only one cell with this name
-}
getCell :: SymbolName -> Term -> Maybe Term
getCell name = para $ \case
    -- Note: para is a variant of cata in which recursive positions
    -- also include the original sub-tree, in addition to the result
    -- of folding that sub-tree.
    targetCell@(SymbolApplicationF symbol _ (children :: [(Term, Maybe Term)]))
        | symbol.name == name -> Just $ embed $ fmap fst targetCell
        | otherwise -> asum $ map snd children
    other -> foldr ((<|>) . snd) Nothing other

{- | Given a term of sort 'K', constructed using 'dotk' and 'kseq'
   (normalised K sequence), return:

  * the head element, with the 'KItem' injection removed, in case of 'kseq'
  * the 'dotk' element in case of 'dotk'
  * @Nothing@ otherwise.
-}
getKSeqHead :: Term -> Maybe Term
getKSeqHead = \case
    app@(SymbolApplication symbol _ args)
        | symbol.name == "kseq"
        , [hd, _tl] <- args ->
            Just $ stripSortInjections hd
        | symbol.name == "dotk"
        , null args ->
            Just app
    _ ->
        Nothing

stripSortInjections :: Term -> Term
stripSortInjections = \case
    Injection _ _ child ->
        stripSortInjections child
    term -> term

-- | indexes terms by their top symbol (combining '\and' branches)
termTopIndex :: Term -> TermIndex
termTopIndex = TermIndex . (: []) . cellTopIndex

{- | Depth-1 indexing of equations: the top symbol of a symbol
application plus one component per argument.

The contract is stated against the tri-state matcher ('matchTerms'
in Eval mode: "matches" / "does not unify" / "indeterminate"), not
against semantic unifiability, and it differs per theory because the
equation-application result handlers differ:

* /Simplifications/ treat every failure mode as "continue", so the
  index may skip any rule whose match cannot return "matches" — both
  decisive failures and indeterminates are skippable.
  Every argument component therefore stays exact ('cellTopIndex').

* /Function equations/ abort on an indeterminate match (protecting
  @[owise]@/priority soundness), so the index may only skip rules
  whose match is guaranteed to /decisively/ fail. Any component whose
  'match1' interaction can be indeterminate (function applications,
  injections, @\\and@) is weakened to @Anything@ on both sides.

Rules whose LHS is not a symbol application keep their single-component
top index; the 'zipWith' truncation in the 'TermIndex' lattice ordering
degrades mixed lengths conservatively.
-}
data EquationTheory = FunctionEquations | Simplifications
    deriving stock (Eq, Show)

{- | Index of an equation LHS (computed once per rule lookup; cheap,
one constructor inspection per argument).
-}
equationLhsIndex :: EquationTheory -> Term -> TermIndex
equationLhsIndex theory = deepIndexWith (equationArgIndex theory)

{- | Index of a subject term for equation candidate filtering.

Identical to the rule-side computation except for bare-variable
arguments in simplification lookup, which become 'IdxVar': a bare
subject variable can never syntactically match a non-variable pattern
component (only bind /pattern/ variables, which are @Anything@), so
'IdxVar' rules out every non-@Anything@ pattern component. For
function equations a bare subject variable is an indeterminate pair
with any pattern, hence @Anything@ (must be attempted).
-}
equationSubjectIndex :: EquationTheory -> Term -> TermIndex
equationSubjectIndex theory = deepIndexWith subjectArg
  where
    subjectArg = case theory of
        FunctionEquations -> equationArgIndex FunctionEquations
        Simplifications -> \case
            Var{} -> IdxVar
            arg -> cellTopIndex arg

deepIndexWith :: (Term -> CellIndex) -> Term -> TermIndex
deepIndexWith argComponent = \case
    t@(SymbolApplication _ _ args) ->
        TermIndex $ cellTopIndex t : map argComponent args
    other ->
        termTopIndex other

-- | Argument component, per theory (see 'equationLhsIndex').
equationArgIndex :: EquationTheory -> Term -> CellIndex
equationArgIndex Simplifications = cellTopIndex
equationArgIndex FunctionEquations = weaken
  where
    -- only shapes whose mismatch 'match1' decides decisively stay
    -- exact; everything that can be indeterminate becomes Anything
    weaken = \case
        ConsApplication symbol _ _ -> IdxCons symbol.name
        DomainValue _ v -> IdxVal v
        KMap{} -> IdxMap
        KList{} -> IdxList
        KSet{} -> IdxSet
        FunctionApplication{} -> Anything
        Var{} -> Anything
        Injection{} -> Anything
        AndTerm{} -> Anything

-- | Cell top indexes form a lattice with a flat partial ordering
cellTopIndex :: Term -> CellIndex
cellTopIndex = \case
    ConsApplication symbol _ _ ->
        IdxCons symbol.name
    FunctionApplication symbol _ _ ->
        IdxFun symbol.name
    DomainValue _ v ->
        IdxVal v
    Var{} ->
        Anything
    KMap{} ->
        IdxMap
    KList{} ->
        IdxList
    KSet{} ->
        IdxSet
    -- look-through
    Injection _ _ t ->
        cellTopIndex t
    AndTerm t1 t2 ->
        cellTopIndex t1 <> cellTopIndex t2
