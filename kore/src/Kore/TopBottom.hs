{-|
Module      : Kore.TopBottom
Description : Class for things that can be top or bottom.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.TopBottom
    ( TopBottom (..)
    ) where

{-| Class for types whose values work as top, bottom, or something between.

'isTop' (respectively 'isBottom') must return 'True' when its argument is
literally top (bottom). @isTop@ and @isBottom@ may return 'False' even if the
argument is semantically equivalent—but not literally equal—to top or bottom.

Instances of 'TopBottom' must satisfy the following laws:

* @'isTop' a@ implies @not ('isBottom' a)@
* @'isBottom' a@ implies @not ('isTop' a)@

-}
class TopBottom term where
    -- | Whether the term works as 'Top'.
    isTop :: term -> Bool
    -- | Whether the term works as 'Bottom'.
    isBottom :: term -> Bool

instance TopBottom () where
    isTop _ = True
    isBottom _ = False
