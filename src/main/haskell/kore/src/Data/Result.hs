{-|
Module      : Data.Result
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Data.Result
    ( Result (..)
    , definite
    , fromResult
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad as Monad

{- | @Result a@ encompasses success, failure, and indeterminacy.

    We may view @Failure@ as indicating a failed attempt, whereas @Unknown@
    indicates that no attempt was made.
 -}
data Result a
    = Success a  -- ^ successful result producing an @a@
    | Failure  -- ^ unsuccessful result
    | Unknown  -- ^ indeterminate result
    deriving (Eq, Ord, Foldable, Functor, Read, Show, Traversable)

-- | Return the result, or the default value if not successful.
fromResult
    :: a  -- ^ default value
    -> Result a  -- ^ result
    -> a
fromResult a =
    \case
        Success a' -> a'
        _ -> a

-- | Make the @Result@ definite, i.e. convert 'Unknown' to 'Failure'.
definite :: Result a -> Result a
definite r = r <|> Failure

instance Applicative Result where
    pure = return
    (<*>) = Monad.ap

instance Monad Result where
    -- | 'Success' is the unit of @>>=@.
    return = Success
    -- | @>>=@ passes a successful result to the next computation. 'Failure' and
    -- 'Unknown' in the left-most position are preserved.
    (>>=) =
        \case
            Success a -> \k -> k a
            Failure -> \_ -> Failure
            Unknown -> \_ -> Unknown

instance Alternative Result where
    -- | 'Unknown' is the identity of @<|>@.
    empty = Unknown
    -- | @<|>@ is left-biased toward 'Success' and 'Failure': either of these
    -- constructors in the left-most position will form the result.
    (<|>) =
        \case
            Success a -> \_ -> Success a
            Failure -> \_ -> Failure
            Unknown -> \r -> r
