{-|
Module      : Template.Tools
Description : Helpers for template Haskell
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

-}
module Template.Tools (newDefinitionGroup) where

import Language.Haskell.TH

-- Begins a new definition group.
--
-- Template Haskell limits the ways in which definitions can be
-- mutually recursive; a quoted name must be defined in a
-- previous definition group before it can be used.
-- A top-level Template Haskell splice always starts a new
-- definition group, even if the splice is empty, as is the
-- case here.
--
-- Without newDefinitionGroup, a declared identifier I would be in scope
-- for expressions, but not for quoting, so using ''I would fail.
--
-- When newDefinitionGroup is placed after the identifier's declaration,
-- the identifier is also visible for quoting in the reminder of the file.
newDefinitionGroup :: Q [Dec]
newDefinitionGroup = return []
