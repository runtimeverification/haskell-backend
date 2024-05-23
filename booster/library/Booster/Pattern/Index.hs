{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Everything to do with term indexing.
-}
module Booster.Pattern.Index (
    TermIndex (..),
    kCellTermIndex,
    termIndexForCell,
    termTopIndex,
) where

import Control.Applicative (Alternative (..), asum)
import Control.DeepSeq (NFData)
import Data.Functor.Foldable (embed, para)
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)

import Booster.Pattern.Base

{- | Index data allowing for a quick lookup of potential axioms.

A @Term@ is indexed by inspecting the top term component of the
head of the K cell. Only constructor and (other) symbol
applications are indexed, all other terms have index @Anything@.

In particular, function applications are treated as opaque, like
variables.

Also, non-free constructors won't get any index, any rules headed by
those can be ignored.

Rather than making the term indexing function partial, we introduce a
unique bottom element @None@ to the index type (to make it a lattice).
This can then handle @AndTerm@ by indexing both arguments and
combining them.

NB for technical reasons we derive an 'Ord' instance but it does not
reflect the fact that different symbols (and likewise different
constructors) are incompatible (partial ordering).
-}
data TermIndex
    = None -- bottom element
    | TopSymbol SymbolName
    | Anything -- top element
    -- should we have  | Value Sort ?? (see Term type)
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

{- | Combines two indexes (an "infimum" function on the index lattice).

  This is useful for terms containing an 'AndTerm': Any term that
  matches an 'AndTerm t1 t2' must match both 't1' and 't2', so 't1'
  and 't2' must have "compatible" indexes for this to be possible.
-}
instance Semigroup TermIndex where
    None <> _ = None
    _ <> None = None
    x <> Anything = x
    Anything <> x = x
    s@(TopSymbol s1) <> TopSymbol s2
        | s1 == s2 = s
        | otherwise = None -- incompatible indexes

{- | Indexes a term by the constructor inside the head of its <k>-cell.

  Only constructors are used, function symbols get index 'Anything'.
-}
kCellTermIndex :: Term -> TermIndex
kCellTermIndex config = termIndexForCell "Lbl'-LT-'k'-GT-'" config

{- | Indexes a term by the head of a K sequence inside a given cell
   (supplied name should have prefix "Lbl'-LT-'" and suffix "'-GT-'").
-}
termIndexForCell :: SymbolName -> Term -> TermIndex
termIndexForCell name config = fromMaybe Anything $ do
    inCell <- getCell name config
    cellArg1 <- firstArgument inCell
    seqHead <- getKSeqHead cellArg1
    pure $ termTopIndex seqHead
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
termTopIndex = \case
    SymbolApplication symbol _ _ ->
        TopSymbol symbol.name
    AndTerm t1 t2 ->
        termTopIndex t1 <> termTopIndex t2
    _other ->
        Anything
