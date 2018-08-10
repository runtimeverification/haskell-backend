{-# LANGUAGE PolyKinds #-}

{-|
Module      : Data.Functor.Impredicative
Description : Wrappers to work around the absence of impredicative types
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Functor.Impredicative where

import Control.DeepSeq
       ( NFData )
import GHC.Generics
       ( Generic )

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
  deriving (Eq, Generic, Show)

instance NFData (t level pat variable) => NFData (Rotate31 t pat variable level)

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
  deriving (Eq, Generic, Show)

instance
    NFData (t level sortParam pat variable) =>
    NFData (Rotate41 t sortParam pat variable level)
