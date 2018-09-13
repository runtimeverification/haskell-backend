{-|
Module      : Kore.Step.Strategy
Description : Strategies for pattern rewriting
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Step.Strategy
    ( -- * Strategies
      Strategy
    , apply
    , stuck
    , and
    , all
    , or
    , any
    , many
    , some
      -- * Running strategies
    , runStrategy
    , pickLongest
    , pickStuck
      -- * Re-exports
    , module Data.Limit
    ) where

import           Data.Bifunctor
                 ( first )
import           Data.List.NonEmpty
                 ( NonEmpty (..) )
import           Data.Semigroup
import           Data.Tree
                 ( Tree )
import qualified Data.Tree as Tree
import           Prelude hiding
                 ( all, and, any, or )

import Control.Monad.Counter
import Data.Limit

{- | An execution strategy.

  @Strategy prim@ represents a strategy for execution by applying rewrite axioms
  of type @prim@.

 -}
data Strategy prim where

    -- The recursive arguments of these constructors are /intentionally/ lazy to
    -- allow strategies to loop.

    Apply :: !prim -> Strategy prim -> Strategy prim

    And :: Strategy prim -> Strategy prim -> Strategy prim

    Stuck :: Strategy prim

    Or :: Strategy prim -> Strategy prim -> Strategy prim

-- | Apply a rewrite axiom.
apply
    :: app
    -- ^ rule
    -> Strategy app
    -- ^ next strategy
    -> Strategy app
apply = Apply

-- | Terminate execution.
stuck :: Strategy app
stuck = Stuck

-- | Apply two strategies in parallel.
and :: Strategy app -> Strategy app -> Strategy app
and = And

{- | Apply all of the strategies in parallel.

  @
  all [] === stuck
  @

 -}
all :: [Strategy app] -> Strategy app
all [] = stuck
all [x] = x
all (x : xs) = and x (all xs)

-- | Apply the second strategy if the first fails.
or :: Strategy app -> Strategy app -> Strategy app
or = Or

{- | Apply the given strategies until one succeeds.

  @
  any [] === stuck
  @

 -}
any :: [Strategy app] -> Strategy app
any [] = stuck
any [x] = x
any (x : xs) = or x (any xs)

-- | Apply the strategy zero or more times.
many :: (Strategy app -> Strategy app) -> Strategy app -> Strategy app
many strategy finally = many0
  where
    many0 = or (strategy many0) finally

-- | Apply the strategy one or more times.
some :: (Strategy app -> Strategy app) -> Strategy app -> Strategy app
some strategy finally = strategy (many strategy finally)

{- | A simple state machine for running 'Strategy'.

  The machine has a primary and secondary instruction pointer and an
  accumulator. The secondary instruction is intended for exception handling.

 -}
data Machine instr accum =
    Machine
        { instrA :: !instr
        -- ^ primary instruction pointer
        , instrB :: !instr
        -- ^ secondary instruction pointer (for exceptions)
        , accum :: !accum
        -- ^ current accumulator
        , stepCount :: !Natural
        -- ^ current step count
        }

-- | Take a step (increment the step counter) if not over the limit.
step :: Limit Natural -> Machine instr accum -> Maybe (Machine instr accum)
step stepLimit state@Machine { stepCount } =
    let
        stepCount' = succ stepCount
    in
        if withinLimit stepLimit stepCount'
            then Just state { stepCount = stepCount' }
            else Nothing

{- | Run a simple state machine.

  The transition rule may allow branching. Returns a tree of all machine states.

 -}
runMachine
    :: Monad m
    => (Machine instr accum -> m [Machine instr accum])
    -- ^ Transition rule
    -> Machine instr accum
    -- ^ Initial state
    -> m (Tree (Machine instr accum))
runMachine transit =
    Tree.unfoldTreeM_BF runMachine0
  where
    runMachine0 state = (,) state <$> transit state

{- | Transition rule for running a 'Strategy' 'Machine'.

  The primitive strategy rule is used to execute the 'Apply' strategy. The
  primitive rule is considered successful if it returns any children and
  considered failed if it returns no children.

 -}
transition
    :: Monad m
    => (prim -> config -> m [config])
    -- ^ Primitive strategy rule
    -> Limit Natural
    -- ^ Step limit
    -> Machine (Strategy prim) config
    -> m [Machine (Strategy prim) config]
transition applyPrim stepLimit =
    \state@Machine { instrA } ->
        case instrA of
            Stuck -> transitionStuck
            And instr1 instr2 -> transitionAnd state instr1 instr2
            Or instr1 instr2 -> transitionOr state instr1 instr2
            Apply prim instrA' -> transitionApply state prim instrA'
  where
    throw state@Machine { instrB } = state { instrA = instrB, instrB = stuck }
    transitionStuck = return []
    transitionAnd state instr1 instr2 =
        -- Distribute the instructions to child branches.
        return
            [ state { instrA = instr1 }
            , state { instrA = instr2 }
            ]
    transitionOr state@Machine{ instrB } instr1 instr2 =
        -- Distribute the instructions to the primary and secondary
        -- instruction pointers.
        return
            [ state
                { instrA = instr1
                -- If instr1 fails, try instr2 and finally instrB.
                , instrB = or instr2 instrB
                }
            ]
    transitionApply state@Machine { accum = config } prim instrA' =
        case step stepLimit state { instrA = instrA' } of
            Nothing -> return [ state { instrA = stuck } ]
            Just state' -> do
                -- Apply a primitive strategy.
                configs <- applyPrim prim config
                case configs of
                    [] ->
                        -- If the primitive failed, throw an exception. Reset
                        -- the exception handler so we do not loop.
                        return [ throw state' ]
                    _ -> do
                        -- If the primitive succeeded, reset the exception
                        -- handler and continue with the children.
                        let next accum = state' { accum, instrB = stuck }
                        return (next <$> configs)

{- | Execute a 'Strategy'.

  The primitive strategy rule is used to execute the 'apply' strategy. The
  primitive rule is considered successful if it returns any children and
  considered failed if it returns no children. The given step limit is applied
  to the primitive strategy rule only; i.e. only 'apply' is considered a step,
  the other strategy combinators are "free".

  The resulting tree of configurations is annotated with the strategy stack at
  each node.

  See also: 'pickFirst'

 -}
runStrategy
    :: Monad m
    => (prim -> config -> m [config])
    -- ^ Primitive strategy rule
    -> Strategy prim
    -- ^ Strategy
    -> Limit Natural
    -- ^ Step limit
    -> config
    -- ^ Initial configuration
    -> m (Tree (Strategy prim, config))
runStrategy applyPrim strategy stepLimit config =
    (<$>) annotateConfig <$> runMachine rule state
  where
    rule = transition applyPrim stepLimit
    state = Machine
        { instrA = strategy
        , instrB = stuck
        , accum = config
        , stepCount = 0
        }
    annotateConfig Machine { instrA, accum } = (instrA, accum)

{- | Pick the longest-running branch from a 'Tree'.

  See also: 'runStrategy'

 -}
pickLongest :: Tree (Strategy prim, config) -> config
pickLongest =
    getLongest . Tree.foldTree pickLongestAt

{- | A 'Semigroup' which returns its longest-running argument.

  See also: 'longest', 'longer'

 -}
newtype Longest a = Longest (Max (Arg Natural a))
    deriving (Semigroup)

getLongest :: Longest a -> a
getLongest (Longest (Max (Arg _ a))) = a

{- | Insert a value into 'Longest' at length 0.
 -}
longest :: a -> Longest a
longest a = Longest (Max (Arg 0 a))

{- | Increase the length of the argument.
 -}
longer :: Longest a -> Longest a
longer (Longest a) = Longest (first succ <$> a)

{- | Pick the longest-running branch at one node of a tree.

  'pickLongest' folds @pickLongestAt@ over an entire tree.

 -}
pickLongestAt :: (instr, config) -> [Longest config] -> Longest config
pickLongestAt (_, config) children =
    sconcat (longest config :| (longer <$> children))

{- | Return all 'stuck' configurations, i.e. all leaves of the 'Tree'.
 -}
pickStuck :: Tree (Strategy prim, config) -> [config]
pickStuck = Tree.foldTree pickStuckAt

pickStuckAt :: (Strategy prim, config) -> [[config]] -> [config]
pickStuckAt (instr, config) children =
    case instr of
        Stuck -> [config]
        _ -> mconcat children
