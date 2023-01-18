{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Everything to do with term indexing.
-}
module Kore.Pattern.Index (
    module Kore.Pattern.Index,
) where

import Control.Applicative (Alternative (..), asum)
import Control.DeepSeq (NFData)
import Data.Functor.Foldable (embed, para)
import GHC.Generics (Generic)

import Kore.Definition.Attributes.Base (SymbolAttributes (..), SymbolType (..))
import Kore.Pattern.Base
import Kore.Pattern.Util qualified as Util

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
combine :: TermIndex -> TermIndex -> TermIndex
combine None _ = None
combine _ None = None
combine x Anything = x
combine Anything x = x
combine s@(TopSymbol s1) (TopSymbol s2)
    | s1 == s2 = s
--     | otherwise = None -- redundant
combine _ _ = None -- incompatible indexes

-- | computes the index of a term
computeTermIndex :: Term -> TermIndex
computeTermIndex config =
    case lookForKCell config of
        Just (SymbolApplication _ _ children) ->
            maybe None getTermIndex (lookForTopTerm (getFirstKCellElem children))
        _ -> Anything
  where
    getTermIndex :: Term -> TermIndex
    getTermIndex term =
        case term of
            SymbolApplication symbol _ _ ->
                case symbol.attributes.symbolType of
                    Constructor -> TopSymbol symbol.name
                    _ -> Anything
            AndTerm term1 term2 ->
                combine (getTermIndex term1) (getTermIndex term2)
            _ -> Anything

    -- it is assumed there is only one K cell
    -- Note: para is variant of cata in which recursive positions also include the original sub-tree,
    -- in addition to the result of folding that sub-tree.
    lookForKCell :: Term -> Maybe Term
    lookForKCell = para $ \case
        kCell@(SymbolApplicationF symbol _ (children :: [(Term, Maybe Term)]))
            | symbol.name == "Lbl'-LT-'k'-GT-'" -> Just $ embed $ fmap fst kCell
            | otherwise -> asum $ map snd children
        other -> foldr ((<|>) . snd) Nothing other

    -- this assumes that the top kseq is already normalized into right-assoc form
    lookForTopTerm :: Term -> Maybe Term
    lookForTopTerm =
        \case
            SymbolApplication symbol _ children
                | symbol.name == "kseq" ->
                    let firstChild = getKSeqFirst children
                     in Just $ stripAwaySortInjections firstChild
                | otherwise ->
                    Nothing -- error ("lookForTopTerm: the first child of the K cell isn't a kseq" <> show symbol.name)
            _other -> Nothing

    -- this assumes that sort injections are well-formed (have a single argument)
    stripAwaySortInjections :: Term -> Term
    stripAwaySortInjections =
        \case
            term@(SymbolApplication symbol _ children) ->
                if Util.isSortInjectionSymbol symbol
                    then stripAwaySortInjections (getInjChild children)
                    else term
            term -> term

    getKSeqFirst [] = error "lookForTopTerm: empty KSeq"
    getKSeqFirst (x : _) = x

    getInjChild [] = error "stripAwaySortInjections: injection with 0 children"
    getInjChild [x] = x
    getInjChild _ = error "stripAwaySortInjections: injection with multiple children"

    getFirstKCellElem [] = error "computeTermIndex: empty K cell"
    getFirstKCellElem (x : _) = x
