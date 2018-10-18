{-|
Module      : Kore.Step.Strategy
Description : Strategies for pattern rewriting
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Step.Strategy
    ( -- * Strategies
      Strategy (..)
    , and
    , all
    , or
    , try
    , any
    , many
    , some
    , apply
    , seq
    , sequence
    , stuck
      -- * Running strategies
    , runStrategy
    , pickLongest
    , pickFinal
    , pickOne
    , pickStar
    , pickPlus
      -- * Re-exports
    , Tree (..)
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
                 ( all, and, any, or, replicate, seq, sequence )

import Control.Monad.Counter

{- | An execution strategy.

    @Strategy prim@ represents a strategy for execution by applying rewrite
    axioms of type @prim@.

    The strategy is represented as a tree where constructor is either a branch
    ('and', 'or'), a continuation ('apply', 'step'), or a termination ('stuck').
    The continutations should be thought of as constructing a linked list where
    the head is a rule to apply and the tail is the rest of the strategy; this
    representation ensures that the root of the strategy tree can always be
    acted upon immediately.

 -}
-- TODO (thomas.tuegel): This could be implemented as an algebra so that a
-- strategy is a free monad over the primitive rule type and the result of
-- execution is not a generic tree, but a cofree comonad with exactly the
-- branching structure described by the strategy algebra.
data Strategy prim where

    -- The recursive arguments of these constructors are /intentionally/ lazy to
    -- allow strategies to loop.

    Seq :: Strategy prim -> Strategy prim -> Strategy prim

    -- | Apply both strategies to the same configuration, i.e. in parallel.
    And :: Strategy prim -> Strategy prim -> Strategy prim

    {- | Apply the second strategy if the first fails immediately.

    A strategy is considered successful if produces any children.
     -}
    Or :: Strategy prim -> Strategy prim -> Strategy prim

    -- | Apply the rewrite rule, then advance to the next strategy.
    Apply :: !prim -> Strategy prim

    Stuck :: Strategy prim

    Continue :: Strategy prim

    deriving (Eq, Show)

{- | Apply two strategies in sequence.

The first strategy is applied, then the second is applied all its children.
 -}
seq :: Strategy prim -> Strategy prim -> Strategy prim
seq = Seq

{- | Apply all of the strategies in sequence.

@
sequence [] === continue
@

 -}
sequence :: [Strategy prim] -> Strategy prim
sequence = foldr seq continue

-- | Apply both strategies to the same configuration, i.e. in parallel.
and :: Strategy prim -> Strategy prim -> Strategy prim
and = And

{- | Apply all of the strategies in parallel.

@
parallel [] === stuck
@

 -}
all :: [Strategy prim] -> Strategy prim
all = foldr and stuck

{- | Apply the second strategy if the first fails immediately.

A strategy is considered successful if it produces any children.
 -}
or :: Strategy prim -> Strategy prim -> Strategy prim
or = Or

{- | Apply the given strategies in order until one succeeds.

A strategy is considered successful if it produces any children.

@
any [] === stuck
@

 -}
any :: [Strategy prim] -> Strategy prim
any = foldr or stuck

-- | Attempt the given strategy once.
try :: Strategy prim -> Strategy prim
try strategy = or strategy continue

-- | Apply the strategy zero or more times.
many :: Strategy prim -> Strategy prim
many strategy = many0
  where
    many0 = or (seq strategy many0) continue

-- | Apply the strategy one or more times.
some :: Strategy prim -> Strategy prim
some strategy = seq strategy (many strategy)

-- | Apply the rewrite rule, then advance to the next strategy.
apply
    :: prim
    -- ^ rule
    -> Strategy prim
apply = Apply

{- | Terminate execution; the end of all strategies.

    @stuck@ does not necessarily indicate unsuccessful termination, but it
    is not generally possible to determine if one branch of execution is
    successful without looking at all the branches.

 -}
stuck :: Strategy prim
stuck = Stuck

continue :: Strategy prim
continue = Continue

{- | Run a simple state machine.

The transition rule may allow branching. Returns a tree of all machine states.

 -}
runMachine
    :: Monad m
    => (instr -> config -> m [config])
    -- ^ Transition rule
    -> [instr]
    -- ^ instructions
    -> config
    -> m (Tree config)
runMachine transit instrs0 config0 =
    Tree.unfoldTreeM_BF runMachine0 (config0, instrs0)
  where
    runMachine0 (config, instrs) =
        case instrs of
            [] -> return (config, [])
            instr : instrs' -> do
                configs <- transit instr config
                return (config, (,) <$> configs <*> pure instrs')

{- | Transition rule for running a 'Strategy'.

The primitive strategy rule is used to execute the 'Apply' strategy. The
primitive rule is considered successful if it returns any children and
considered failed if it returns no children.

 -}
transitionRule
    :: Monad m
    => (prim -> config -> m [config])
    -- ^ Primitive strategy rule
    -> Strategy prim
    -> config
    -> m [config]
transitionRule applyPrim = transitionRule0
  where
    transitionRule0 =
        \case
            Seq instr1 instr2 -> transitionSeq instr1 instr2
            And instr1 instr2 -> transitionAnd instr1 instr2
            Or instr1 instr2 -> transitionOr instr1 instr2
            Apply prim -> transitionApply prim
            Continue -> transitionContinue
            Stuck -> transitionStuck

    -- End execution.
    transitionStuck _ = return []

    transitionContinue config = return [config]

    -- Apply the instructions in sequence.
    transitionSeq instr1 instr2 config0 = do
        configs1 <- transitionRule0 instr1 config0
        concat <$> mapM (transitionRule0 instr2) configs1

    -- Attempt both instructions, i.e. create a branch for each.
    transitionAnd instr1 instr2 config =
        (++)
            <$> transitionRule0 instr1 config
            <*> transitionRule0 instr2 config

    -- Attempt the first instruction. Fall back to the second if it is
    -- unsuccessful.
    transitionOr instr1 instr2 config =
        transitionRule0 instr1 config >>=
            \case
                [] -> transitionRule0 instr2 config
                configs -> return configs

    -- Apply a primitive rule. Throw an exception if the rule is not successful.
    transitionApply prim config =
        applyPrim prim config

{- | Execute a 'Strategy'.

The primitive strategy rule is used to execute the 'apply' strategy. The
primitive rule is considered successful if it returns any children and
considered failed if it returns no children.

The strategies are applied in sequence. The 'rootLabel' of is the initial
configuration and the 'subForest' are the children returned by the first
strategy in the list; the tree is unfolded likewise by recursion.

See also: 'pickFirst'

 -}
runStrategy
    :: Monad m
    => (prim -> config -> m [config])
    -- ^ Primitive strategy rule
    -> [Strategy prim]
    -- ^ Strategies
    -> config
    -- ^ Initial configuration
    -> m (Tree config)
runStrategy applyPrim = runMachine (transitionRule applyPrim)

{- | Pick the longest-running branch from a 'Tree'.

  See also: 'runStrategy'

 -}
pickLongest :: Tree config -> config
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
pickLongestAt :: config -> [Longest config] -> Longest config
pickLongestAt config children =
    sconcat (longest config :| (longer <$> children))

{- | Return all 'stuck' configurations, i.e. all leaves of the 'Tree'.
 -}
pickFinal :: Tree config -> [config]
pickFinal = Tree.foldTree pickFinalAt

pickFinalAt :: config -> [[config]] -> [config]
pickFinalAt config children =
    case children of
        [] -> [config]
        _ -> mconcat children

{- | Return all configurations reachable in one step.
 -}
pickOne :: Tree config -> [config]
pickOne tree = Tree.rootLabel <$> Tree.subForest tree

{- | Return all reachable configurations.
 -}
pickStar :: Tree config -> [config]
pickStar = foldr (:) []

{- | Return all configurations reachable after at least one step.
 -}
pickPlus :: Tree config -> [config]
pickPlus = foldr (flip (foldr (:))) [] . Tree.subForest
