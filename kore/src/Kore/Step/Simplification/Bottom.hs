{-|
Module      : Kore.Step.Simplification.Bottom
Description : Tools for Bottom pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.Bottom
    ( simplify
    ) where

import Prelude.Kore ()

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Kore.Sort
import Kore.Syntax.Bottom

{-| simplifies a Bottom pattern, which means returning an always-false or.
-}
simplify :: Bottom Sort child -> OrPattern RewritingVariableName
simplify Bottom {} = OrPattern.bottom
