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
module Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SmtMetadataTools
    , extractMetadataTools
    , isConstructorOrOverloaded
    , findSortConstructors
    ) where

import Data.Function
    ( on
    )
import Data.Graph
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( mapMaybe
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import Kore.Attribute.Subsort
import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
    ( Symbol
    )
import qualified Kore.Internal.Symbol as Symbol
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
    , isSubsortOf :: Sort -> Sort -> Bool
    {- ^ @isSubsortOf a b@ is true if sort @a@ is a subsort of sort @b@,
       including when @a@ equals @b@. -}
    , subsorts :: Sort -> Set Sort
    -- ^ get the subsorts for a sort
    , applicationSorts :: SymbolOrAlias -> ApplicationSorts
    -- ^ Sorts for a specific symbol application.
    , symbolAttributes :: Id -> attributes
    -- ^ get the attributes of a symbol
    , isOverloading :: Symbol -> Symbol -> Bool
    -- ^ whether the first argument is overloading the second
    , isOverloaded :: Symbol -> Bool
    -- ^ Whether the symbol is overloaded
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
    ::  forall declAtts smt sortConstructors.
        VerifiedModule declAtts Attribute.Axiom
    ->  (  VerifiedModule declAtts Attribute.Axiom
        -> Map Id sortConstructors
        )
    ->  (  VerifiedModule declAtts Attribute.Axiom
        -> Map Id sortConstructors
        -> smt
        )
    -> MetadataTools sortConstructors smt declAtts
extractMetadataTools m constructorsExtractor smtExtractor =
    MetadataTools
        { sortAttributes = getSortAttributes m
        , isSubsortOf = checkSubsort
        , subsorts = Set.fromList . fmap getSortFromId . getSubsorts
        , applicationSorts = getHeadApplicationSorts m
        , symbolAttributes = getSymbolAttributes m
        , isOverloading = checkOverloading `on` Symbol.toSymbolOrAlias
        , isOverloaded = checkOverloaded . Symbol.toSymbolOrAlias
        , smtData = smtExtractor m constructors
        , sortConstructors = constructors
        }
  where
    subsortTable :: Map Sort [Sort]
    subsortTable = Map.unionsWith (++)
        [ Map.insert subsort [] $ Map.singleton supersort [subsort]
        | Subsort subsort supersort <- indexedModuleSubsorts m]

    constructors = constructorsExtractor m

    -- In `sortGraph`, an edge (a, b) represents a subsort relationship between
    -- b and a.
    (sortGraph, vertexToSort, sortToVertex) =
        graphFromEdges [ ((),supersort,subsorts)
                        | (supersort,subsorts)
                            <- Map.toList subsortTable]
    getSortFromId :: Vertex -> Sort
    getSortFromId sortId =
        let (_, sort, _) = vertexToSort sortId
        in sort

    getSubsorts :: Sort -> [Vertex]
    getSubsorts = maybe [] (reachable sortGraph) . sortToVertex

    checkSubsort :: Sort -> Sort -> Bool
    checkSubsort =
        let
            realCheckSubsort subsort supersort
              | Just subId <- sortToVertex subsort
              , Just supId <- sortToVertex supersort =
                path sortGraph supId subId
            realCheckSubsort _ _ = False
        in realCheckSubsort

    overloadPairsSet = Set.fromList overloadPairsList

    overloadPairsList =
        mapMaybe
            (Attribute.getOverload . Attribute.overload . fst)
            (recursiveIndexedModuleAxioms m)

    allOverloadsList = concatMap (\(o1, o2) -> [o1,o2]) overloadPairsList

    allOverloadsSet = Set.fromList allOverloadsList

    checkOverloaded :: SymbolOrAlias -> Bool
    checkOverloaded = (`Set.member` allOverloadsSet)

    checkOverloading :: SymbolOrAlias -> SymbolOrAlias -> Bool
    checkOverloading head1 head2 = (head1, head2) `Set.member` overloadPairsSet

-- |Checks whether symbol is constructor or overloaded
isConstructorOrOverloaded
    :: SmtMetadataTools Attribute.Symbol
    -> Symbol
    -> Bool
isConstructorOrOverloaded tools s =
    Symbol.isConstructor s || isOverloaded tools s

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
