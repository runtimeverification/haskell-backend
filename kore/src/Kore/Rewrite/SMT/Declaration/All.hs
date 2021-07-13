{- |
Module      : Kore.Rewrite.SMT.Declaration.All
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Declaration.All (
    declare,
) where

import qualified Kore.Rewrite.SMT.AST as AST (
    SmtDeclarations,
 )
import qualified Kore.Rewrite.SMT.Declaration.Sorts as Sorts (
    declare,
 )
import qualified Kore.Rewrite.SMT.Declaration.Symbols as Symbols (
    declare,
 )
import Prelude.Kore ()
import qualified SMT

-- | Sends all given declarations to the SMT.
declare :: SMT.MonadSMT m => AST.SmtDeclarations -> m ()
declare declarations = do
    Sorts.declare declarations
    Symbols.declare declarations
