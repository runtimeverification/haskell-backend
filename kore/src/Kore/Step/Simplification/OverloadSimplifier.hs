{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Step.Simplification.OverloadSimplifier
    ( OverloadSimplifier (..)
    , mkOverloadSimplifier
    ) where

import Control.Exception
    ( assert
    )
import Data.Maybe
    ( listToMaybe
    )
import qualified GHC.Stack as GHC

import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.IndexedModule.OverloadGraph
    ( OverloadGraph
    )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import Kore.IndexedModule.SortGraph
    ( SortGraph
    , isSubsortOf
    )
import Kore.Internal.ApplicationSorts
    ( applicationSortsResult
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike

data OverloadSimplifier =
    OverloadSimplifier
        { isOverloading :: Symbol -> Symbol -> Bool
        -- ^ Whether the first argument is overloading the second
        , isOverloaded :: Symbol -> Bool
        -- ^ Whether the symbol is overloaded
        , resolveOverloading
            :: forall variable
            .  GHC.HasCallStack
            => InternalVariable variable
            => Inj ()
            -> Symbol
            -> [TermLike variable]
            -> TermLike variable
        -- ^ Apply an overloading equation
        , unifyOverloadWithinBound :: Symbol -> Symbol -> Sort -> Maybe Symbol
        -- ^ Find a common overload with result sort a subsort of the argument
        }

mkOverloadSimplifier
    :: OverloadGraph
    -> SortGraph
    -> OverloadSimplifier
mkOverloadSimplifier overloadGraph sortGraph =
    OverloadSimplifier
        { isOverloading
        , isOverloaded
        , resolveOverloading
        , unifyOverloadWithinBound
        }
  where
    isOverloading = OverloadGraph.isOverloading overloadGraph
    isOverloaded = OverloadGraph.isOverloaded overloadGraph

    resolveOverloading injProto overloadedHead overloadingChildren =
        mkApplySymbol overloadedHead
        $ assert (length overloadedChildrenSorts == length overloadingChildren)
        $ zipWith mkInj overloadingChildren overloadedChildrenSorts
      where
        overloadedChildrenSorts =
            Symbol.applicationSortsOperands (symbolSorts overloadedHead)
        mkInj injChild injTo =
            (synthesize . InjF) injProto { injFrom, injTo, injChild }
          where
            injFrom = termLikeSort injChild

    unifyOverloadWithinBound s1 s2 topSort =
        listToMaybe withinBound
      where
        withinBound =
            filter (\x -> isSubsortOf sortGraph (resultSort x) topSort)
                (OverloadGraph.commonOverloads overloadGraph s1 s2)

    resultSort :: Symbol -> Sort
    resultSort = applicationSortsResult  . symbolSorts
