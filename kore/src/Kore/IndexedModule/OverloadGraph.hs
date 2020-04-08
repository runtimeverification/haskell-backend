{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.IndexedModule.OverloadGraph
    ( OverloadGraph
    , isOverloaded
    , isOverloading
    , commonOverloads
    , fromIndexedModule
    --
    , fromOverloads
    ) where

import Prelude.Kore

import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , recursiveIndexedModuleAxioms
    )
import Kore.Internal.Symbol

{- | 'OverloadGraph' maps symbols to symbols overloading them
 -}
newtype OverloadGraph = OverloadGraph { unOverloadGraph :: Map Symbol (Set Symbol) }
    deriving (GHC.Generic, Typeable)

instance SOP.Generic OverloadGraph

instance SOP.HasDatatypeInfo OverloadGraph

instance Debug OverloadGraph

instance Diff OverloadGraph

-- | Whether the symbol is an overloading symbol
isOverloaded :: OverloadGraph -> Symbol -> Bool
isOverloaded graph s =  s ` Map.member` unOverloadGraph graph

-- | Whether the first symbol overloads the second
isOverloading :: OverloadGraph -> Symbol -> Symbol -> Bool
isOverloading graph s1 s2
     | Just ss <- unOverloadGraph graph Map.!? s2
     = s1 `Set.member` ss
     | otherwise = False

-- | List of symbols overloading both symbol arguments
commonOverloads :: OverloadGraph -> Symbol -> Symbol -> [Symbol]
commonOverloads graph sym1 sym2 =
    maybe [] Set.toList
        (Set.intersection
            <$> (unOverloadGraph graph Map.!? sym1)
            <*> (unOverloadGraph graph Map.!? sym2)
        )

{- | Build a 'OverloadGraph' from a list of overloaded symbol pairs.

  The list of overloaded symbol pairs given as an argument is assumed
  to represent the _transitive closure_ of the overloading relation.
 -}
fromOverloads
    :: [(Symbol, Symbol)]  -- ^ first symbol overloads the second
    -> OverloadGraph
fromOverloads overloadPairsList =
    let allOverloadsList = concatMap (\(o1, o2) -> [o1,o2]) overloadPairsList
        allOverloadsSet = Set.fromList allOverloadsList
    in OverloadGraph $ Map.fromSet superOverloading allOverloadsSet
  where
    superOverloading subOverloading =
        Set.fromList [x | (x, y) <- overloadPairsList, y == subOverloading]

{- | Builds an overload graph from the @overload@ attribute annotations
associated to overloading equations in a verified module.

Assumes the overloading relation is already transitive.

-}
fromIndexedModule
    :: VerifiedModule Attribute.Symbol
    -> OverloadGraph
fromIndexedModule verifiedModule = fromOverloads overloadPairList
  where
    overloadPairList = preOverloadPairsList
    preOverloadPairsList =
        mapMaybe
            (Attribute.getOverload . Attribute.overload . fst)
            (recursiveIndexedModuleAxioms verifiedModule)
