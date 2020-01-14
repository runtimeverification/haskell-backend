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
import Data.Function
    ( on
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( listToMaybe
    , mapMaybe
    )
import qualified Data.Set as Set
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , recursiveIndexedModuleAxioms
    )
import Kore.IndexedModule.MetadataTools as MetadataTools
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
        -- ^ whether the first argument is overloading the second
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
        , unifyOverloadWithinBound :: Symbol -> Symbol -> Sort -> Maybe Symbol
        }

mkOverloadSimplifier
    :: VerifiedModule Attribute.Symbol Attribute.Axiom
    -> SortGraph
    -> SmtMetadataTools Attribute.StepperAttributes
    -> OverloadSimplifier
mkOverloadSimplifier verifiedModule sortGraph tools =
    OverloadSimplifier
        { isOverloading
        , isOverloaded
        , resolveOverloading
        , unifyOverloadWithinBound
        }
  where
    isOverloading = checkOverloading `on` Symbol.toSymbolOrAlias
    isOverloaded = checkOverloaded . Symbol.toSymbolOrAlias

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

    checkOverloaded :: SymbolOrAlias -> Bool
    checkOverloaded = (`Set.member` allOverloadsSet)

    checkOverloading :: SymbolOrAlias -> SymbolOrAlias -> Bool
    checkOverloading head1 head2 = (head1, head2) `Set.member` overloadPairsSet

    overloadPairsSet = Set.fromList overloadPairsList

    overloadPairsList =
        mapMaybe
            (Attribute.getOverload . Attribute.overload . fst)
            (recursiveIndexedModuleAxioms verifiedModule)

    allOverloadsList = concatMap (\(o1, o2) -> [o1,o2]) overloadPairsList

    allOverloadsSet = Set.fromList allOverloadsList

    unifyOverloadWithinBound s1 s2 topSort =
        symbolOrAliasToSymbol <$> listToMaybe withinBound
      where
        sa1 = Symbol.toSymbolOrAlias s1
        sa2 = Symbol.toSymbolOrAlias s2
        withinBound =
            filter (\x -> isSubsortOf sortGraph (resultSort x) topSort)
                (commonOverloads sa1 sa2)
        symbolOrAliasToSymbol sym = s1
            { symbolConstructor = symbolOrAliasConstructor sym
            , symbolParams = symbolOrAliasParams sym
            , symbolSorts = MetadataTools.applicationSorts tools sym
            }

    resultSort :: SymbolOrAlias -> Sort
    resultSort = applicationSortsResult  . MetadataTools.applicationSorts tools

    superOverloading :: SymbolOrAlias -> Set.Set SymbolOrAlias
    superOverloading subOverloading =
        Set.fromList [x | (x, y) <- overloadPairsList, y == subOverloading]

    superOverloadingMap :: Map.Map SymbolOrAlias (Set.Set SymbolOrAlias)
    superOverloadingMap =
        Map.fromAscList
        $ map (\x -> (x, superOverloading x)) (Set.toAscList allOverloadsSet)

    commonOverloads :: SymbolOrAlias -> SymbolOrAlias -> [SymbolOrAlias]
    commonOverloads sym1 sym2 =
        maybe [] Set.toList
            (Set.intersection
                <$> (superOverloadingMap Map.!? sym1)
                <*> (superOverloadingMap Map.!? sym2)
            )

