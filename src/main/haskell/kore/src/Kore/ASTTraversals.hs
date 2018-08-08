{-|
Module      : Kore.ASTTraversals
Description : Defines traversals functions for patterns of
              `UnifiedPatternInterface` class.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module provides a specialization of some functionality from
the 'Data.Functor.Foldable' module to the case of Kore patterns.

This specialization is meant to allow the user to functions
taking a 'Pattern', and transform a 'KorePattern' or any
other type implementing 'UnifiedPatternInterface'.
-}
module Kore.ASTTraversals
    ( patternBottomUpVisitor
    ) where

import Data.Functor.Foldable
       ( Fix, cata )

import Kore.AST.Common
       ( Pattern, UnifiedPatternInterface, unifiedPatternApply )
import Kore.AST.MetaOrObject
       ( MetaOrObject )

-- |'patternBottomUpVisitor' is @cata . unifiedPatternApply@

patternBottomUpVisitor
    :: (UnifiedPatternInterface pat, Functor (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable result -> result)
    -> (Fix (pat variable) -> result)
patternBottomUpVisitor reduce = cata (unifiedPatternApply reduce)
