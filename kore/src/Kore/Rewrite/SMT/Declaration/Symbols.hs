{- |
Module      : Kore.Rewrite.SMT.Declaration.Symbols
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Declaration.Symbols (
    declare,
) where

import qualified Kore.Rewrite.SMT.AST as AST (
    Declarations (Declarations),
    KoreSymbolDeclaration (SymbolBuiltin, SymbolConstructor, SymbolDeclaredDirectly),
    SmtDeclarations,
    SmtKoreSymbolDeclaration,
    SmtSymbol,
    Symbol (Symbol),
 )
import qualified Kore.Rewrite.SMT.AST as AST.DoNotUse
import Prelude.Kore
import qualified SMT

-- | Sends all symbols in the given declarations to the SMT.
declare :: SMT.MonadSMT m => AST.SmtDeclarations -> m ()
declare AST.Declarations{symbols} = traverse_ declareSymbol symbols

declareSymbol :: SMT.MonadSMT m => AST.SmtSymbol -> m ()
declareSymbol AST.Symbol{declaration} =
    declareKoreSymbolDeclaration declaration

declareKoreSymbolDeclaration ::
    SMT.MonadSMT m => AST.SmtKoreSymbolDeclaration -> m ()
declareKoreSymbolDeclaration
    (AST.SymbolDeclaredDirectly declaration) =
        SMT.declareFun_ declaration
declareKoreSymbolDeclaration (AST.SymbolBuiltin _) =
    return ()
declareKoreSymbolDeclaration (AST.SymbolConstructor _) =
    return ()
