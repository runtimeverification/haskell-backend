{-|
Module      : Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# LANGUAGE Strict #-}
module Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SmtMetadataTools
    , extractMetadataTools
    , findSortConstructors
    ) where

import Prelude.Kore

import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts
import Kore.Sort
import qualified Kore.Step.SMT.AST as SMT.AST
    ( SmtDeclarations
    )
import Kore.Syntax.Application
    ( SymbolOrAlias (..)
    )

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools sortConstructors smt attributes = MetadataTools
    { sortAttributes :: Sort -> Attribute.Sort
    -- ^ get the attributes of a sort
    , applicationSorts :: SymbolOrAlias -> ApplicationSorts
    -- ^ Sorts for a specific symbol application.
    , symbolAttributes :: Id -> attributes
    -- ^ get the attributes of a symbol
    , smtData :: smt
    -- ^ The SMT data for the given module.
    , sortConstructors :: Map Id sortConstructors
    -- ^ The constructors for each sort.
    }
  deriving Functor

type SmtMetadataTools attributes =
    MetadataTools Attribute.Constructors SMT.AST.SmtDeclarations attributes

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as its attributes or
-- its argument and result sorts.
--
extractMetadataTools
    :: forall declAtts smt sortConstructors.
       VerifiedModule declAtts
    -> (VerifiedModule declAtts -> Map Id sortConstructors)
    -> (VerifiedModule declAtts -> Map Id sortConstructors -> smt)
    -> MetadataTools sortConstructors smt declAtts
extractMetadataTools m constructorsExtractor smtExtractor =
    MetadataTools
        { sortAttributes = getSortAttributes m
        , applicationSorts = getHeadApplicationSorts m
        , symbolAttributes = getSymbolAttributes m
        , smtData = smtExtractor m constructors
        , sortConstructors = constructors
        }
  where
    constructors = constructorsExtractor m

{-| Extracts all constructors for a sort.

Should return Nothing if the sort has no constructors or if the sort has no
constructors, or `inj` behaves like a constructor, but the latter is only true
if the constructor axioms actually include `inj` when needed, which is not true
right now.
-}
findSortConstructors
    :: SmtMetadataTools attributes -> Id -> Maybe Attribute.Constructors
findSortConstructors
    MetadataTools {sortConstructors}
    sortId
  = Map.lookup sortId sortConstructors
