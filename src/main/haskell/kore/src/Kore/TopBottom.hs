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

isTop and isBottom are allowed to return False when the term is Top/Bottom,
but that's not easily identifiable.
-}
class TopBottom term where
    -- | Whether the term works as 'Top'.
    isTop :: term -> Bool
    -- | Whether the term works as 'Bottom'.
    isBottom :: term -> Bool

instance TopBottom ()
  where
    isTop _ = True
    isBottom _ = False
