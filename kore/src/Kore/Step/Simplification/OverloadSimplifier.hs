{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Step.Simplification.OverloadSimplifier
    ( OverloadSimplifier (..)
    , mkOverloadSimplifier
    ) where

import Prelude.Kore

import Kore.IndexedModule.OverloadGraph
    ( OverloadGraph
    )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import Kore.Internal.ApplicationSorts
    ( applicationSortsResult
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.InjSimplifier
    ( InjSimplifier (..)
    )

{- | Data structure encapsulating functionality for handling overloaded
symbols during unification.
-}
data OverloadSimplifier =
    OverloadSimplifier
        { isOverloading :: Symbol -> Symbol -> Bool
        -- ^ Whether the first argument is overloading the second
        , isOverloaded :: Symbol -> Bool
        -- ^ Whether the symbol is overloaded
        , resolveOverloading
            :: forall variable
            .  HasCallStack
            => InternalVariable variable
            => Inj ()
            -> Symbol
            -> [TermLike variable]
            -> TermLike variable
        {- ^ Apply an overloading equation from right to left.

        In general an overloading equation is of the form

        @overloadingOp(inj{S1,S2}(X:S1)) = inj{S,S'}(overloadedOp(X:S1))@

        This function is given an injection prototype (used for name and
        attributes), the @overloadingOp@ symbol and the list of children
        corresponding to the @overloadedOp@ symbol application (@X:S1@ in the
        example above).  It then injects the children appropriately to serve
        as arguments to @overloadingOp@ and applies @overloadingOp@ to them.
        -}
        , unifyOverloadWithinBound
            :: Inj ()
            -> Symbol
            -> Symbol
            -> Sort
            -> Maybe (Symbol, Maybe (Inj ()))
        {- ^ Find a common overload with the result sort being a subsort of the
        argument, if such an overload exists. Also returns the appropriate
        injection, if necessary.
        -}
        }

{- | Builds an Overload Simplifier given a graph encoding the overload
relation and one encoding the subsort relation. The latter is needed for
'unifyOverloadWithinBound'.
-}
mkOverloadSimplifier
    :: OverloadGraph
    -> InjSimplifier
    -> OverloadSimplifier
mkOverloadSimplifier overloadGraph InjSimplifier {isOrderedInj, injectTermTo} =
    OverloadSimplifier
        { isOverloading
        , isOverloaded
        , resolveOverloading
        , unifyOverloadWithinBound
        }
  where
    isOverloading = OverloadGraph.isOverloading overloadGraph
    isOverloaded = OverloadGraph.isOverloaded overloadGraph

    resolveOverloading
        :: forall variable
        .  HasCallStack
        => InternalVariable variable
        => Inj ()
        -> Symbol
        -> [TermLike variable]
        -> TermLike variable
    resolveOverloading injProto overloadedHead overloadingChildren =
        mkApplySymbol overloadedHead
        $ assert (length overloadedChildrenSorts == length overloadingChildren)
        $ zipWith mkInj overloadingChildren overloadedChildrenSorts
      where
        mkInj = injectTermTo injProto
        overloadedChildrenSorts =
            Symbol.applicationSortsOperands (symbolSorts overloadedHead)

    unifyOverloadWithinBound injProto s1 s2 topSort =
        headMay withinBound
      where
        injProtoTop = injProto { injTo = topSort }
        withinBound =
            map (fmap
                    (\inj ->
                        if injFrom inj == injTo inj then Nothing else Just inj
                    )
                )
            . filter (isOrderedInj . snd)
            . map (\x -> (x, injProtoTop { injFrom = resultSort x }))
            $ OverloadGraph.commonOverloads overloadGraph s1 s2

    resultSort :: Symbol -> Sort
    resultSort = applicationSortsResult  . symbolSorts
