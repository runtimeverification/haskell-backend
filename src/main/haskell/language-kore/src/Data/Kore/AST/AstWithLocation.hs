{-|
Module      : Data.Kore.AST.AstWithLocation
Description : Class for extracting locations from AST terms.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Kore.AST.AstWithLocation (AstWithLocation(..)) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject

{-| 'AstWithLocation' should be implemented by all AST terms that have
an 'AstLocation'.
-}
class AstWithLocation awl where
    locationFromAst :: awl -> AstLocation

instance
    (AstWithLocation (thing Object), AstWithLocation (thing Meta))
    => AstWithLocation (Unified thing)
  where
    locationFromAst (UnifiedObject t) = locationFromAst t
    locationFromAst (UnifiedMeta t)   = locationFromAst t

instance AstWithLocation AstLocation where
    locationFromAst = id

instance AstWithLocation (Id level) where
    locationFromAst = idLocation

instance AstWithLocation (SortVariable level) where
    locationFromAst = locationFromAst . getSortVariable

instance AstWithLocation (SortActual level) where
    locationFromAst = locationFromAst . sortActualName

instance AstWithLocation (Sort level) where
    locationFromAst (SortVariableSort sortVariable) =
        locationFromAst sortVariable
    locationFromAst (SortActualSort sortActual) =
        locationFromAst sortActual

instance AstWithLocation (Variable level) where
    locationFromAst = locationFromAst . variableName
