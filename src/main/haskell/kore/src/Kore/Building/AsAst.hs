{-|
Module      : Kore.Building.AsAst
Description : Class for things that can be transformed into AST terms.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Building.AsAst where

class AsAst a b where
    asAst :: b -> a
