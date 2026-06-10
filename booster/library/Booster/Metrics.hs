{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Process-global accumulator for per-rule equation timing.

Every equation application attempt records its wall time (monotonic
clock, nanoseconds) split into match and condition-discharge phases,
keyed by the rule's unique id. The accumulator is flushed and reported
once per JSON-RPC request (see 'Booster.JsonRpc'), giving per-rule
seconds with near-zero overhead and no log volume — the cheap
complement to per-entry capture timestamps.

The accumulator is process-global (like 'Booster.GlobalState'), so
concurrently processed requests would mix their numbers; requests are
normally handled one at a time, and the report is attribution data,
not a correctness surface.
-}
module Booster.Metrics (
    RuleMetrics (..),
    ruleAttempt,
    recordRuleAttempt,
    flushRuleMetrics,
) where

import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Word (Word64)
import System.IO.Unsafe (unsafePerformIO)

import Booster.Definition.Attributes.Base (UniqueId)

-- | Cumulative per-rule counters; times are monotonic-clock nanoseconds.
data RuleMetrics = RuleMetrics
    { attempts :: !Int
    , successes :: !Int
    , totalNs :: !Word64
    -- ^ whole attempt spans, including substitution and result construction
    , matchNs :: !Word64
    -- ^ time spent in the syntactic matcher
    , conditionNs :: !Word64
    -- ^ time spent discharging requires/ensures clauses (including
    -- recursive equation application and SMT)
    }

instance Semigroup RuleMetrics where
    a <> b =
        RuleMetrics
            { attempts = a.attempts + b.attempts
            , successes = a.successes + b.successes
            , totalNs = a.totalNs + b.totalNs
            , matchNs = a.matchNs + b.matchNs
            , conditionNs = a.conditionNs + b.conditionNs
            }

-- | A single attempt with the given outcome and phase times.
ruleAttempt :: Bool -> Word64 -> Word64 -> Word64 -> RuleMetrics
ruleAttempt success totalNs matchNs conditionNs =
    RuleMetrics
        { attempts = 1
        , successes = if success then 1 else 0
        , totalNs
        , matchNs
        , conditionNs
        }

{-# NOINLINE ruleMetrics #-}
ruleMetrics :: IORef (Map UniqueId RuleMetrics)
ruleMetrics = unsafePerformIO $ newIORef Map.empty

recordRuleAttempt :: UniqueId -> RuleMetrics -> IO ()
recordRuleAttempt uid m =
    atomicModifyIORef' ruleMetrics $ \stats -> (Map.insertWith (<>) uid m stats, ())

-- | Read the accumulated metrics and reset the accumulator.
flushRuleMetrics :: IO (Map UniqueId RuleMetrics)
flushRuleMetrics = atomicModifyIORef' ruleMetrics (Map.empty,)
