{- |
Module      : Kore.Rewrite.SMT.Declaration.Sorts
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Declaration.Sorts (
    declare,
) where

import qualified Data.Map.Strict as Map
import qualified Kore.Rewrite.SMT.AST as AST (
    Declarations (Declarations),
    KoreSortDeclaration (SortDeclarationDataType, SortDeclarationSort, SortDeclaredIndirectly),
    SmtDeclarations,
    SmtSort,
    Sort (Sort),
 )
import qualified Kore.Rewrite.SMT.AST as SMT.AST.DoNotUse
import Prelude.Kore
import qualified SMT

-- | Sends all sorts in the given declarations to the SMT.
declare :: SMT.MonadSMT m => AST.SmtDeclarations -> m ()
declare AST.Declarations{sorts} = do
    mapM_ SMT.declareSort sortDeclarations
    SMT.declareDatatypes dataTypeDeclarations
  where
    sortDeclarations :: [SMT.SmtSortDeclaration]
    dataTypeDeclarations :: [SMT.SmtDataTypeDeclaration]
    (sortDeclarations, dataTypeDeclarations) =
        partitionEithers (mapMaybe eitherDeclaration (Map.elems sorts))

    eitherDeclaration ::
        AST.SmtSort ->
        Maybe (Either SMT.SmtSortDeclaration SMT.SmtDataTypeDeclaration)
    eitherDeclaration
        AST.Sort
            { declaration = AST.SortDeclarationSort declaration
            } =
            Just (Left declaration)
    eitherDeclaration
        AST.Sort
            { declaration = AST.SortDeclarationDataType declaration
            } =
            Just (Right declaration)
    eitherDeclaration
        AST.Sort
            { declaration = AST.SortDeclaredIndirectly _
            } =
            Nothing
