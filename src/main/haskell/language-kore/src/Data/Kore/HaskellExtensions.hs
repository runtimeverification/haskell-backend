{-# LANGUAGE PolyKinds #-}
module Data.Kore.HaskellExtensions where

import           Data.Typeable

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
  deriving (Typeable, Eq, Show)

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
  deriving (Typeable, Eq, Show)

{-|The '<..>' operator offers function composition functionality when the
second function has two arguments.  It satisfies that

* @(g <..> f) a1 a2 == g (f a1 a2)@
-}
(<..>) :: (b -> c) -> (a1 -> a2 -> b) -> (a1 -> a2 -> c)
(<..>) = (.) . (.)

{-|The '<...>' operator offers function composition functionality when the
second function has two arguments.  It satisfies that

* @(g <...> f) a1 a2 a3 == g (f a1 a2 a3)@
-}
(<...>) :: (b -> c) -> (a1 -> a2 -> a3 -> b) -> (a1 -> a2 -> a3 -> c)
(<...>) = (<..>) . (.)

{-|The '<....>' operator offers function composition functionality when the
second function has two arguments.  It satisfies that

* @(g <...> f) a1 a2 a3 a4 == g (f a1 a2 a3 a4)@
-}
(<....>)
    :: (b -> c)
    -> (a1 -> a2 -> a3 -> a4 -> b)
    -> (a1 -> a2 -> a3 -> a4 -> c)
(<....>) = (<...>) . (.)
