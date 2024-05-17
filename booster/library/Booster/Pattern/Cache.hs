{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Cache (
    cacheTerm,
    clearTermCache,
) where

import Control.Concurrent (MVar)
import Control.Concurrent qualified as C
import Data.Functor (void)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as M
import System.IO.Unsafe (unsafePerformIO)

import Booster.Pattern.Base (Term)

{- | Global term cache, avoids duplicating terms

* The cache contains all terms that have been constructed, as a hash map of terms to themselves.
* concurrency is handled by using an MVar as a mutex holding the cache.
-}
termCacheVar :: MVar (HashMap Term Term)
termCacheVar = unsafePerformIO $ putStrLn "[DEBUG] making a term cache" >> C.newMVar mempty
{-# NOINLINE termCacheVar #-}

{- | The cache is manually managed at the moment, it requires regular
clearing to avoid RAM growth of the server. In the presence of
concurrent requests, this means that if the first request clears the
cache, any other requests in flight lose the sharing of all terms
stored in that cache before. Everything will continue to work, though.
-}
clearTermCache :: IO ()
clearTermCache = void $ C.swapMVar termCacheVar mempty
{-# INLINE clearTermCache #-}

{- | Cache a constructed term, i.e., replace it by the cached version if
   one exists, or else add it to the cache and return the argument.
-}
cacheTermIO :: Term -> IO Term
cacheTermIO !t =
    C.modifyMVar termCacheVar $ \cache ->
        case M.lookup t cache of
            Nothing -> do
                let !newCache = M.insert t t cache
                pure (newCache, t)
            Just t' -> pure (cache, t') -- t is now garbage

cacheTerm :: Term -> Term
cacheTerm = unsafePerformIO . cacheTermIO
{-# INLINE cacheTerm #-}
{-# INLINE cacheTermIO #-}
