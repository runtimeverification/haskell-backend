{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.AsVariable where

class AsVariable f where
    asVariable :: f variable -> variable
