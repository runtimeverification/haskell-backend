{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Simplification.Inj
    ( simplify
    ) where

import Prelude.Kore

import Data.Functor.Compose

import Kore.Internal.Condition as Condition
import Kore.Internal.MultiOr
    ( MultiOr
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InjSimplifier
    ( InjSimplifier (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier

{- |'simplify' simplifies an 'Inj' of 'OrPattern'.

-}
simplify
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Inj (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify injOrPattern = do
    let composed = Compose . fmap liftConditional $ distributeOr injOrPattern
    InjSimplifier { evaluateInj } <- askInjSimplifier
    let evaluated = evaluateInj <$> composed
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
