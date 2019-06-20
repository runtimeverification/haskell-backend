{-|
Module      : Kore.Step.RecursiveAttributes
Description : Tools for using pattern attributes in step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.RecursiveAttributes
    ( isFunctionalPattern
    , isFunctionPattern
    , isTotalPattern
    ) where

import Kore.Internal.TermLike
