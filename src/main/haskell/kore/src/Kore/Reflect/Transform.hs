{-|
Module      : Kore.Reflect.Transform
Description : Infrastructure for transforming reflected objects.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Reflect.Transform
    ( NodeTransformation (..)
    , Position (..)
    , Transformation (..)
    , delete
    , descend
    , transform
    ) where

import Data.Foldable
       ( foldl' )
import Data.Functor.Foldable
       ( Fix (..), fold )

import           Kore.Reflect
                 ( Data, ProductElement (ProductElement), RecursiveData )
import qualified Kore.Reflect as Reflect

{-| Wraps a Data transformer.
-}
newtype Transformer = Transformer (Data RecursiveData -> Data RecursiveData)

{-| Identifies a single level in RecursiveData
-}
data Position
    = Name !String
    -- ^ Matches a Data object with the given name.
    | Index !Int
    -- ^ Matches a Data object with the given 0-based index.
    -- Note that an index cannot be matched as the top-level element,
    -- it needs a parent.
    | Value
    -- ^ Matches a Value Data object.
    | Any
    -- ^ Matches any Data object.

{-| A transformation of a Data (sub)tree.

If the position matches a given node, then the transformer is applied,
after which the postFilters are applied on the children.
-}
data NodeTransformation = NodeTransformation
    { position :: !Position
    , transformer :: !(Maybe Transformer)
    , postFilters :: !Transformation
    }

{-| A transformation wraps multiple possible transformations for a node. They
are applied in the given order, skipping the ones that do not match the node.
-}
newtype Transformation = Transformation [NodeTransformation]

{-| Transforms an entire tree in a bottom-up fashion, using the given
transformation.
-}
transform :: Transformation -> RecursiveData -> RecursiveData
transform transformations = fold (applyTransformations transformations)

applyTransformations
    :: Transformation -> Data RecursiveData -> RecursiveData
applyTransformations transformations node =
    Fix $ dataWithTransformation 0 node transformations

dataWithTransformation
    :: Int -> Data RecursiveData -> Transformation -> Data RecursiveData
dataWithTransformation index node (Transformation transformations) =
    foldl' (dataWithNodeTransformation index) node transformations

dataWithNodeTransformation
    :: Int
    -> Data RecursiveData
    -> NodeTransformation
    -> Data RecursiveData
dataWithNodeTransformation
    index
    node
    NodeTransformation {position, transformer = filter0, postFilters}
  | match position index node =
    transformNodeChildren (filterNode filter0 node) postFilters
  | otherwise = node

match :: Position -> Int -> Data RecursiveData -> Bool
match (Name searchedName) _index (Reflect.Sum ProductElement {name = sumName})
  = sumName == searchedName
match
    (Name searchedName)
    _index
    (Reflect.Struct ProductElement {name = structName})
  = structName == searchedName
match (Name searchedName) _index (Reflect.StructField fieldName _value)
  = fieldName == searchedName
match (Name _) _index (Reflect.Value _) = False
match (Name _) _index (Reflect.List _)  = False
match (Name _) _index (Reflect.Tuple _) = False
match (Name _) _index Reflect.Deleted   = False

match (Index searchedIndex) index _node = index == searchedIndex

match Value _index (Reflect.Sum _)           = False
match Value _index (Reflect.Struct _)      = False
match Value _index (Reflect.StructField _ _) = False
match Value _index (Reflect.Value _)         = True
match Value _index (Reflect.List _)          = False
match Value _index (Reflect.Tuple _)         = False
match Value _index Reflect.Deleted           = False

match Any _index Reflect.Deleted = False
match Any _index _node           = True

transformNodeChildren
    :: Data RecursiveData -> Transformation -> Data RecursiveData
transformNodeChildren
    (Reflect.Sum ProductElement {name, values})
    transformation
  =
    Reflect.Sum ProductElement {name, values = newValues}
  where
    newValues = transformValues 0 values transformation
transformNodeChildren
    (Reflect.Struct ProductElement { name, values })
    transformation
  =
    Reflect.Struct ProductElement {name, values = newValues}
  where
    newValues = transformValues 0 values transformation
transformNodeChildren
    (Reflect.StructField fieldName (Fix value))
    transformation
  =
    Reflect.StructField fieldName newValue
  where
    newValue = Fix (dataWithTransformation 0 value transformation)
transformNodeChildren
    n@(Reflect.Value _)
    _
  = n
transformNodeChildren
    (Reflect.List values)
    transformation
  =
    Reflect.List newValues
  where
    newValues = transformValues 0 values transformation
transformNodeChildren
    (Reflect.Tuple values)
    transformation
  =
    Reflect.Tuple newValues
  where
    newValues = transformValues 0 values transformation
transformNodeChildren
    Reflect.Deleted
    _transformation
  =
    Reflect.Deleted

filterNode
    :: Maybe Transformer -> Data RecursiveData -> Data RecursiveData
filterNode Nothing d = d
filterNode (Just (Transformer filter0)) d = filter0 d

transformValues
    :: Int
    -> [RecursiveData]
    -> Transformation
    -> [RecursiveData]
transformValues _ [] _ = []
transformValues index (Fix value : values) transformation =
    ( Fix (dataWithTransformation index value transformation)
    : transformValues (index + 1) values transformation
    )

deleteFilter :: Data RecursiveData -> Data RecursiveData
deleteFilter = const Reflect.Deleted

{-| Node transformation for deleting a node.
-}
delete :: Position -> NodeTransformation
delete position =
    NodeTransformation
        { position
        , transformer = Just (Transformer deleteFilter)
        , postFilters = Transformation []
        }

{-| Node transformation that matches a node, does not transform it, but may
transform its children.
-}
descend :: Position -> Transformation -> NodeTransformation
descend position transformation =
    NodeTransformation
        {position, transformer = Nothing, postFilters = transformation}
