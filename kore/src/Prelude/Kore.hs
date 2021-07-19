{- |
Copyright : (c) 2020 Runtime Verification
License   : BSD-3-Clause
-}
module Prelude.Kore (
    module Prelude,
    module Debug.Trace,

    -- * Ord
    minMax,
    minMaxBy,

    -- * Functions
    (&),
    on,
    (<&>),

    -- * Maybe
    isJust,
    isNothing,
    fromMaybe,
    headMay,

    -- * Either
    either,
    fromLeft,
    fromRight,
    isLeft,
    isRight,
    partitionEithers,

    -- * Filterable
    Filterable (..),

    -- * Witherable
    Witherable (..),

    -- * Errors
    HasCallStack,
    assert,

    -- * Applicative and Alternative
    Applicative (..),
    Alternative (..),
    optional,

    -- * From
    module From,

    -- * Comonad
    module Control.Comonad,
    Cofree,
    CofreeF (..),

    -- * Hashable
    Hashable (..),

    -- * NFData
    NFData (..),

    -- * Monad
    Monad (..),
    MonadPlus (..),
    MonadIO (..),
    MonadTrans (..),
    void,
    unless,
    when,

    -- * Typeable
    Typeable,

    -- * Injection
    module Injection,

    -- * Category
    Category (..),
    (<<<),
    (>>>),

    -- * Semigroup
    Semigroup (..),

    -- * NonEmpty
    NonEmpty (..),

    -- * Tuple
    module Data.Tuple,

    -- * Foldable
    module Data.Foldable,

    -- * Traversable
    module Data.Traversable,
) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.
import Control.Applicative (
    Alternative (..),
    Applicative (..),
    optional,
 )
import Control.Category (
    Category (..),
    (<<<),
    (>>>),
 )
import Control.Comonad
import Control.Comonad.Trans.Cofree (
    Cofree,
    CofreeF (..),
 )
import Control.DeepSeq (
    NFData (..),
 )
import Control.Error (
    either,
    headMay,
    isLeft,
    isRight,
 )
import Control.Exception (
    assert,
 )
import Control.Monad (
    Monad (..),
    MonadPlus (..),
    unless,
    when,
 )
import Control.Monad.IO.Class (
    MonadIO (..),
 )
import Control.Monad.Trans.Class (
    MonadTrans (..),
 )
import Data.Either (
    fromLeft,
    fromRight,
    partitionEithers,
 )
import Data.Foldable
import Data.Function (
    on,
    (&),
 )
import Data.Functor (
    void,
    (<&>),
 )
import Data.Hashable (
    Hashable (..),
 )
import Data.List.NonEmpty (
    NonEmpty (..),
 )
import Data.Maybe (
    fromMaybe,
    isJust,
    isNothing,
 )
import Data.Semigroup (
    Semigroup (..),
 )
import Data.Traversable
import Data.Tuple
import Data.Typeable (
    Typeable,
 )
import Data.Witherable (
    Filterable (..),
    Witherable (..),
 )
import Debug.Trace hiding (
    traceEvent,
    traceEventIO,
 )
import From
import GHC.Stack (
    HasCallStack,
 )
import Injection
import Prelude hiding (
    Applicative (..),
    Monad (..),
    either,
    filter,
    id,
    log,
    (.),
 )

-- | Simultaneously compute the (@min@, @max@) of two values.
minMax :: Ord a => a -> a -> (a, a)
minMax a b
    | a < b = (a, b)
    | otherwise = (b, a)

minMaxBy :: (a -> a -> Ordering) -> a -> a -> (a, a)
minMaxBy cmp a b
    | cmp a b == LT = (a, b)
    | otherwise = (b, a)
