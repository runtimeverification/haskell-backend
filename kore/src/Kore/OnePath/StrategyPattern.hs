module Kore.OnePath.StrategyPattern
    ( StrategyPattern (..)
    , strategyPattern
    , StrategyPatternTransformer (..)
    , CommonStrategyPattern
    , extractUnproven
    , extractStuck
    ) where

import Data.Hashable
import GHC.Generics

import Kore.Internal.Pattern
       ( Pattern )
import Kore.Internal.TermLike

{- | A pattern on which a rule can be applied or on which a rule was applied.

As an example, when rewriting

@
if x then phi else psi
@

with these rules

@
if true  then u else v => u
if false then u else v => v
@

there would be two 'RewritePattern's, @phi and x=true@ and @psi and x=false@.
If only the first rule was present, the results would be a 'RewritePattern' with
@phi and x=true@ and a 'Remainder' with @psi and not x=true@.

When rewriting the same pattern with an rule that does not match, e.g.

@
x + y => x +Int y
@

then rewriting produces no children.

-}
data StrategyPattern patt
    = RewritePattern !patt
    -- ^ Pattern on which a normal 'Rewrite' can be applied. Also used
    -- for the start patterns.
    | Stuck !patt
    -- ^ Pattern which can't be rewritten anymore.
    | Bottom
    -- ^ special representation for a bottom rewriting/simplification result.
    -- This is needed when bottom results are expected and we want to
    -- differentiate between them and stuck results.
  deriving (Show, Eq, Ord, Generic)

{- | Extract the unproven part of a 'StrategyPattern'.

Returns 'Nothing' if there is no remaining unproven part.

 -}
extractUnproven :: StrategyPattern patt -> Maybe patt
extractUnproven (RewritePattern p) = Just p
extractUnproven (Stuck          p) = Just p
extractUnproven Bottom             = Nothing

-- | Extract the 'Stuck' part of a 'StrategyPattern'.
extractStuck :: StrategyPattern patt -> Maybe patt
extractStuck (Stuck p) = Just p
extractStuck _         = Nothing

data StrategyPatternTransformer patt a =
    StrategyPatternTransformer
        { rewriteTransformer :: patt -> a
        , stuckTransformer :: patt -> a
        , bottomValue :: a
        }

-- | Catamorphism for 'StrategyPattern'
strategyPattern
    :: StrategyPatternTransformer patt a
    -> StrategyPattern patt
    -> a
strategyPattern
    StrategyPatternTransformer
        {rewriteTransformer, stuckTransformer, bottomValue}
  =
    \case
        RewritePattern patt -> rewriteTransformer patt
        Stuck patt -> stuckTransformer patt
        Bottom -> bottomValue

-- | A 'StrategyPattern' instantiated to 'Pattern Variable' for convenience.
type CommonStrategyPattern = StrategyPattern (Pattern Variable)

instance Hashable patt => Hashable (StrategyPattern patt)
