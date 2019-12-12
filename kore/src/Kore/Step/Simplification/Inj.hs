{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Simplification.Inj
    ( simplify
    ) where

import Data.Functor.Compose

import Kore.Internal.Condition as Condition
import Kore.Internal.Inj
    ( Inj (..)
    )
import Kore.Internal.MultiOr
    ( MultiOr
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InjSimplifier
    ( simplifyInj
    )
import Kore.Step.Simplification.Simplify as Simplifier

{- |'simplify' simplifies an 'Inj' of 'OrPattern'.

-}
simplify
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Inj (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify _ injOrPattern = do
    let composed = Compose . fmap liftConditional $ distributeOr injOrPattern
    injSimplifier <- askInjSimplifier
    let evaluated = simplifyInj injSimplifier <$> composed
    return (getCompose evaluated)

distributeOr
    :: Inj (MultiOr a)
    -> MultiOr (Inj a)
distributeOr = sequenceA

liftConditional
    :: InternalVariable variable
    => Inj (Conditional variable term)
    -> Conditional variable (Inj term)
liftConditional = sequenceA
