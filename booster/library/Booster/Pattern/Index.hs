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
    -- shortcut to abort rewriting/evaluation
    hasNone,
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

The @CellIndex@ of a cell containing a @SymbolApplication@ node is the
symbol at the top. Other terms that are not symbol applications have
index @Anything@.

Rather than making the term indexing function partial, we introduce a
unique bottom element @None@ to the index type (to make it a lattice).
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
    = None -- bottom element
    | TopCons SymbolName
    | TopFun SymbolName
    | TopVal ByteString
    | TopMap
    | TopList
    | TopSet
    | Anything -- top element
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

{- | Index lattice class. This is mostly just a _flat lattice_ but also
  needs to support a special 'invert' method for the subject term index.
-}
class IndexLattice a where
    (^<=^) :: a -> a -> Bool

    invert :: a -> a

ifGreater :: IndexLattice a => Set a -> a -> Set a
ifGreater base x = Set.filter (x ^<=^) base

{- | Partial less-or-equal for CellIndex (implies partial order)

                Anything
   ____________/   |  \_______________________________________...
  /          /     |            |           \             \
TopList ..TopSet  TopVal "x"..TopVal "y"  TopCons "A"..  TopFun "f"..
  \__________|__   |  _________|____________|____________/____...
                \  | /
                 None
-}
instance IndexLattice CellIndex where
    None ^<=^ _ = True
    a ^<=^ None = a == None
    _ ^<=^ Anything = True
    Anything ^<=^ a = a == Anything
    a ^<=^ b = a == b

    invert None = Anything
    invert Anything = None
    invert a = a

-- | Partial less-or-equal for TermIndex (product lattice)
instance IndexLattice TermIndex where
    TermIndex idxs1 ^<=^ TermIndex idxs2 = and $ zipWith (^<=^) idxs1 idxs2

    invert (TermIndex idxs) = TermIndex (map invert idxs)

{- | Combines two indexes (an "infimum" function on the index lattice).

  This is useful for terms containing an 'AndTerm': Any term that
  matches an 'AndTerm t1 t2' must match both 't1' and 't2', so 't1'
  and 't2' must have "compatible" indexes for this to be possible.
-}
instance Semigroup CellIndex where
    None <> _ = None
    _ <> None = None
    x <> Anything = x
    Anything <> x = x
    idx1 <> idx2
        | idx1 == idx2 = idx1
        | otherwise = None

-- | Pretty instances
instance Pretty TermIndex where
    pretty (TermIndex ixs) = sep $ map pretty ixs

instance Pretty CellIndex where
    pretty None = "_|_"
    pretty Anything = "***"
    pretty (TopCons sym) = "C--" <> prettyLabel sym
    pretty (TopFun sym) = "F--" <> prettyLabel sym
    pretty (TopVal sym) = "V--" <> prettyLabel sym
    pretty TopMap = "Map"
    pretty TopList = "List"
    pretty TopSet = "Set"

prettyLabel :: ByteString -> Doc a
prettyLabel = either error ( pretty . unpack) . decodeLabel


{- | Check whether a @TermIndex@ has @None@ in any position (this
means no match will be possible).
-}
hasNone :: TermIndex -> Bool
hasNone (TermIndex ixs) = None `elem` ixs

{- | Computes all indexes that "cover" the given index, for rule lookup.

  An index B is said to "cover" an index A if all components of B are
  greater or equal to those of the respective component of A inverted.

  * For components of A that are distinct from @Anything@, this means
    the component of B is equal to that of A or @Anything@.
  * For components of A that are @None@, the respective component of B
    _must_ be @Anything@. However, if A contains @None@ no match is
    possible anyway.
  * For components of A that are @Anything@, B can contain an
    arbitrary index (@None@ will again have no chance of a match,
    though).

  When selecting candidate rules for a term, we must consider all
  rules whose index has either the exact same @CellIndex@ or
  @Anything@ at every position of their @TermIndex@.
-}
covering :: Set TermIndex -> TermIndex -> Set TermIndex
covering prior ix = prior `ifGreater` invert ix

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

-- | Cell top indexes form a lattice with a flat partial ordering
cellTopIndex :: Term -> CellIndex
cellTopIndex = \case
    ConsApplication symbol _ _ ->
        TopCons symbol.name
    FunctionApplication symbol _ _ ->
        TopFun symbol.name
    DomainValue _ v ->
        TopVal v
    Var{} ->
        Anything
    KMap{} ->
        TopMap
    KList{} ->
        TopList
    KSet{} ->
        TopSet
    -- look-through
    Injection _ _ t ->
        cellTopIndex t
    AndTerm t1 t2 ->
        cellTopIndex t1 <> cellTopIndex t2
