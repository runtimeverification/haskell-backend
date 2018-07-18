{-|
Module      : Data.Kore.ASTTraversals
Description : Generic functionality to circumvent some issues occuring due to
              the order of types in Haskell.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.HaskellExtensions
    (Rotate31(..), Rotate41(..)
    , (<..>), (<...>), (<....>)
    , ReversedList, reversedAdd, reversedToList, emptyReversedList)
  where

{-|'Rotate31' is a helper type useful to bring the first argument
of a type paramaterized by three arguments to the last position,
shifting the other arguments to the left.

For example, 'Rotate41' might be needed to transform types in order
to use such 'MetaOrObject' constructs as 'applyMetaObjectFunction' or
'UnifiedThing'.
-}
newtype
    Rotate31 t pat variable level
  = Rotate31 { unRotate31 :: t level pat variable}
  deriving (Eq, Show)

{-|'Rotate41' is a helper type useful to bring the first argument
of a type paramaterized by four arguments to the last position,
shifting the other arguments to the left.

For example, 'Rotate41' might be needed to transform types in order
to use such 'MetaOrObject' constructs as 'applyMetaObjectFunction' or
'UnifiedThing'.
-}
newtype
    Rotate41 t sortParam pat variable level
  = Rotate41 { unRotate41 :: t level sortParam pat variable}
  deriving (Eq, Show)

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

newtype ReversedList a = ReversedList [a]
    deriving (Show, Eq)

reversedAdd :: a -> ReversedList a -> ReversedList a
reversedAdd e (ReversedList l) = ReversedList (e:l)

reversedToList :: ReversedList a -> [a]
reversedToList (ReversedList l) = reverse l

emptyReversedList :: ReversedList a
emptyReversedList = ReversedList []
