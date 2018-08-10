{-|
Module      : Data.Function.Compose
Description : Short-hand notation for function composition with many arguments
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Data.Function.Compose where

{-|The '<..>' operator offers function composition functionality when the
second function has two arguments.  It satisfies that

* @(g <..> f) a1 a2 == g (f a1 a2)@
-}
(<..>) :: (b -> c) -> (a1 -> a2 -> b) -> (a1 -> a2 -> c)
(<..>) = (.) . (.)

{-|The '<...>' operator offers function composition functionality when the
second function has three arguments.  It satisfies that

* @(g <...> f) a1 a2 a3 == g (f a1 a2 a3)@
-}
(<...>) :: (b -> c) -> (a1 -> a2 -> a3 -> b) -> (a1 -> a2 -> a3 -> c)
(<...>) = (<..>) . (.)

{-|The '<....>' operator offers function composition functionality when the
second function has four arguments.  It satisfies that

* @(g <...> f) a1 a2 a3 a4 == g (f a1 a2 a3 a4)@
-}
(<....>)
    :: (b -> c)
    -> (a1 -> a2 -> a3 -> a4 -> b)
    -> (a1 -> a2 -> a3 -> a4 -> c)
(<....>) = (<...>) . (.)
