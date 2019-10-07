{-|
Module      : Kore.Step.SMT.Declaration.Symbols
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Declaration.Symbols
    ( declare
    ) where

import qualified Data.Foldable as Foldable

import qualified Kore.Step.SMT.AST as AST
    ( Declarations (Declarations)
    , KoreSymbolDeclaration (SymbolBuiltin, SymbolConstructor, SymbolDeclaredDirectly)
    , SmtDeclarations
    , SmtKoreSymbolDeclaration
    , SmtSymbol
    , Symbol (Symbol)
    )
import qualified Kore.Step.SMT.AST as AST.DoNotUse
import qualified SMT

{-| Sends all symbols in the given declarations to the SMT.
-}
declare :: SMT.MonadSMT m => AST.SmtDeclarations -> m ()
declare AST.Declarations { symbols } =
    Foldable.traverse_ declareSymbol symbols

declareSymbol :: SMT.MonadSMT m => AST.SmtSymbol -> m ()
declareSymbol AST.Symbol {declaration} =
    declareKoreSymbolDeclaration declaration

declareKoreSymbolDeclaration
    :: SMT.MonadSMT m => AST.SmtKoreSymbolDeclaration -> m ()
declareKoreSymbolDeclaration
    (AST.SymbolDeclaredDirectly declaration)
  =
    SMT.declareFun_ declaration
declareKoreSymbolDeclaration (AST.SymbolBuiltin _) =
    return ()
declareKoreSymbolDeclaration (AST.SymbolConstructor _) =
    return ()
