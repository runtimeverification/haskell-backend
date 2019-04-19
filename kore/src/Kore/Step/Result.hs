{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}

module Kore.Step.Result
    ( Result (..)
    , Results (..)
    , remainder
    , withoutRemainders
    , gatherResults
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import           Data.Sequence
                 ( Seq )
import qualified GHC.Generics as GHC

import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.TopBottom
                 ( TopBottom )

-- | The result of applying a single rule.
data Result rule config =
    Result
        { appliedRule :: !rule
        , result      :: !(MultiOr config)
        }
    deriving (Eq, GHC.Generic, Ord, Show)

{- | The results of applying many rules.

The rules may be applied in sequence or in parallel and the 'remainders' vary
accordingly.

 -}
data Results rule config =
    Results
        { results :: !(Seq (Result rule config))
        , remainders :: !(MultiOr config)
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance (Ord config, TopBottom config) => Semigroup (Results rule config) where
    (<>) results1 results2 =
        Results
            { results = Function.on (<>) results results1 results2
            , remainders = Function.on (<>) remainders results1 results2
            }

instance (Ord config, TopBottom config) => Monoid (Results rule config) where
    mempty = Results { results = mempty, remainders = mempty }
    mappend = (<>)

{- | Take the 'Results' without any 'remainders'.
 -}
withoutRemainders
    :: (Ord config, TopBottom config)
    => Results rule config
    -> Results rule config
withoutRemainders results = results { remainders = mempty }

{- | 'Results' consisting of one remainder and no results.
 -}
remainder :: (Ord config, TopBottom config) => config -> Results rule config
remainder config = mempty { remainders = MultiOr.singleton config }

{- | Gather all the final configurations from the 'Results'.
 -}
gatherResults
    :: (Ord config, TopBottom config)
    => Results rule config
    -> MultiOr config
gatherResults = Foldable.fold . fmap result . results
