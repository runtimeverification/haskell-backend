{-|
Module      : Kore.Step.SMT.Declaration.All
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Declaration.All
    ( declare
    ) where

import qualified Kore.Step.SMT.AST as AST
    ( SmtDeclarations
    )
import qualified Kore.Step.SMT.Declaration.Sorts as Sorts
    ( declare
    )
import qualified Kore.Step.SMT.Declaration.Symbols as Symbols
    ( declare
    )
import qualified SMT

{-| Sends all given declarations to the SMT.
-}
declare :: SMT.MonadSMT m => AST.SmtDeclarations -> m ()
declare declarations = do
    Sorts.declare declarations
    Symbols.declare declarations
