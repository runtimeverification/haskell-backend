{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Simplification.Inj
    ( simplify
    ) where

import Prelude.Kore

import Data.Functor.Identity
    ( runIdentity
    )

import Kore.Internal.Condition as Condition
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InjSimplifier
    ( InjSimplifier (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom
    ( TopBottom
    )
import qualified Logic

{- |'simplify' simplifies an 'Inj' of 'OrPattern'.

-}
simplify
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Inj (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify injOrPattern = do
    let composed = MultiOr.map liftConditional $ distributeOr injOrPattern
    InjSimplifier { evaluateInj } <- askInjSimplifier
    let evaluated = MultiOr.map (fmap evaluateInj) composed
    return evaluated

distributeOr
    :: Ord a
    => TopBottom a
    => Inj (MultiOr a)
    -> MultiOr (Inj a)
distributeOr inj@Inj { injChild } =
    runIdentity . MultiOr.observeAllT $ do
        child <- Logic.scatter injChild
        return inj { injChild = child }

liftConditional
    :: InternalVariable variable
    => Inj (Conditional variable term)
    -> Conditional variable (Inj term)
liftConditional = sequenceA
