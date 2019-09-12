{-|
Module      : Kore.Step.SMT.Resolvers
Description : Translates sorts and symbols to a SMT representation.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.SMT.Resolvers
    (translateSymbol) where

import qualified Data.Map as Map
import Data.Reflection
    ( Given
    , given
    )

import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (MetadataTools)
    , SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
    ( MetadataTools (smtData)
    )
import Kore.Internal.Symbol
import qualified Kore.Step.SMT.AST as AST
    ( Declarations (Declarations)
    , Symbol (Symbol)
    )
import qualified Kore.Step.SMT.AST as AST.DoNotUse
import qualified SMT

{-| Creates the SMT representation of a symbol assuming the smt declarations in
the given SmtMetadataTools.
-}
translateSymbol
    :: Given (SmtMetadataTools Attribute.Symbol)
    => Symbol
    -> Maybe SMT.SExpr
translateSymbol Symbol { symbolConstructor, symbolParams } = do
    AST.Symbol { smtFromSortArgs } <- Map.lookup symbolConstructor symbols
    smtFromSortArgs sorts symbolParams
  where
    MetadataTools {smtData = AST.Declarations {sorts, symbols}} = tools

    tools :: SmtMetadataTools Attribute.Symbol
    tools = given
