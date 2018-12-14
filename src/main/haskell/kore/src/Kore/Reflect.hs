{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
{- |
Module      : Kore.Reflect
Description : Reflection for generic data structures.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This offers an easier interface than GHC.Generics

To allow reflection for some data type:

@
import GHC.Generics ( Generic )
import Kore.Reflect (Reflectable)

data MyData = ...
    deriving (Generic)

instance Reflectable MyData
@

To reflect a value:

@
import Kore.Reflect (Reflectable(reflect))

myFunc value = reflect value
@

-}
module Kore.Reflect
    ( Data (..)
    , ProductElement (..)
    , RecursiveData
    , Reflectable (..)
    , mkDeleted
    , mkList
    , mkRawStruct
    , mkStruct
    , mkStructField
    , mkSum
    , mkTuple
    , mkValue
    , printData
    ) where

-- TODO:  Move the package outside of Kore

import           Control.Comonad.Trans.Cofree
                 ( Cofree, CofreeF (..), CofreeT (CofreeT) )
import           Data.Eq.Deriving
                 ( deriveEq1 )
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Foldable
                 ( Fix (..) )
import           Data.Functor.Identity
                 ( Identity (Identity) )
import           Data.Hashable
                 ( Hashable )
import           Data.List
                 ( intercalate )
import qualified Data.Map as Map
import           Data.Sequence
                 ( Seq )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Constructor, Datatype, Fixity (..), Generic, Selector )
import qualified GHC.Generics as Generics
import           Numeric.Natural
                 ( Natural )
import           Text.Show.Deriving
                 ( deriveShow1 )

{-| A reflected element that has a name and any number of values,
including none, e.g. product types.
-}
data ProductElement v = ProductElement {name :: !String, values :: ![v]}
    deriving (Eq, Functor, Generic, Show)

deriveEq1 ''ProductElement
deriveShow1 ''ProductElement

instance Hashable v => Hashable (ProductElement v)

{-| One level of a reflected value, with v as the value's children.

As an example, when reflecting

@
SomeStruct {someField1 = value1, someField1 = value2}
@

then data would contain the representation of

@
SomeStruct {someField1 = ?, someField1 = ?}
@

with the value of question marks depending on the v parameter.
-}
data Data v
    = Sum !(ProductElement v)
    -- ^ Represents a value of the form (Name childValue1 ... childValue_n)
    | Struct !(ProductElement v)
    | StructField !String !v
    -- ^ Represents struct value.
    | Value !String
    -- ^ Represents a leaf value, i.e. one without children
    | List ![v]
    -- ^ Represents a list of values
    | Tuple ![v]
    -- ^ Represents a tuple of values
    | Deleted
    -- ^ Represents data that was deleted.
    deriving (Eq, Functor, Generic, Show)

deriveEq1 ''Data
deriveShow1 ''Data

instance Hashable v => Hashable (Data v)

{-| A reflected value.
-}
type RecursiveData = Fix Data

{-| Class for things that can be represented as 'RecursiveData'.

For any instance of Generic, if the data's "children" (see below) are
Reflectable, the 'reflect' fuction is automatically implemented and the
derivation looks something like:

@
instance
    (constraints-to-make-MyData-generic)
    => (Reflectable MyData)
@

A data type's children are, roughly, the parts that are not declared in
that data's declaration. Examples:

@
data MyData = MyData T1 T2
-- Children: T1 and T2

data MyData = MyData {f1 :: T1, f2 :: T2}
-- Children: T1 and T2
@
-}
class Reflectable a where
    reflect :: a -> RecursiveData
    default reflect
        :: (Generic a, Reflectable' (Generics.Rep a)) => a -> RecursiveData
    reflect x = reflect' (Generics.from x)

instance {-# OVERLAPS #-} Reflectable String where
    reflect = Fix . Value . show

instance Reflectable Text where
    reflect = Fix . Value . show

instance Reflectable Char where
    reflect = Fix . Value . show

instance Reflectable Int where
    reflect = Fix . Value . show

instance Reflectable Integer where
    reflect = Fix . Value . show

instance Reflectable Natural where
    reflect = Fix . Value . show

instance Reflectable () where
    reflect = Fix . Value . show

instance Reflectable (Const Void a) where
    reflect a = case a of {}

instance {-# OVERLAPPABLE #-} (Reflectable a) => Reflectable [a] where
    reflect = Fix . List . map reflect

instance (Reflectable a, Reflectable b) => Reflectable (Map.Map a b) where
    reflect = Fix . List . map reflect . Map.toList

instance (Reflectable a) => Reflectable (Set.Set a) where
    reflect = Fix . List . map reflect . Set.toList

instance (Reflectable a) => Reflectable (Seq a) where
    reflect = Fix . List . map reflect . Foldable.toList

instance (Reflectable a1, Reflectable a2) => Reflectable (a1, a2) where
    reflect (a1, a2) = Fix $ Tuple [reflect a1, reflect a2]

instance (Reflectable a1, Reflectable a2, Reflectable a3)
    => Reflectable (a1, a2, a3)
  where
    reflect (a1, a2, a3) = Fix $ Tuple [reflect a1, reflect a2, reflect a3]

instance (Reflectable a1, Reflectable a2, Reflectable a3, Reflectable a4)
    => Reflectable (a1, a2, a3, a4)
  where
    reflect (a1, a2, a3, a4) =
        Fix $ Tuple [reflect a1, reflect a2, reflect a3, reflect a4]

instance (Reflectable a) => Reflectable (Maybe a) where
    reflect (Just a) = mkSum "Just" [reflect a]
    reflect Nothing = mkSum "Nothing" []

instance (Reflectable a1, Reflectable a2) => Reflectable (Either a1 a2) where
    reflect (Left a) = mkSum "Left" [reflect a]
    reflect (Right a) = mkSum "Right" [reflect a]

instance
    (Reflectable (a (Cofree a b)), Reflectable b)
    => Reflectable (Cofree a b)
  where
    reflect (CofreeT (Identity (b :< a))) =
        mkSum "Cofree" [reflect b, reflect a]

-----------------------------------
--      Generic reflection       --
-----------------------------------

class Reflectable' f where
    reflect' :: f p -> RecursiveData

class ReflectableFields f where
    reflectStructFields :: f p -> [RecursiveData]
    reflectProductValues :: f p -> [RecursiveData]

-- TODO: Maybe separate ReflectableFields based on their "K1 R a" content.
instance (Reflectable a) => Reflectable' (Generics.K1 Generics.R a) where
    reflect' (Generics.K1 a) = reflect a

instance
    (Selector metadata, Reflectable' child)
    => ReflectableFields (Generics.M1 Generics.S metadata child)
  where
    -- TODO: Add a ReflectableField for this.
    reflectStructFields m@(Generics.M1 thing) =
        if null name
            then error "Unexpected null name"
            else [Fix (StructField name (reflect' thing))]
      where
        name = Generics.selName m
    reflectProductValues m@(Generics.M1 thing) =
        if null name
            then [reflect' thing]
            else error ("Unexpected name: " ++ show name)
      where
        name = Generics.selName m

instance ReflectableFields Generics.U1
  where
    -- TODO: Add a ReflectableField for this.
    reflectStructFields _ = []
    reflectProductValues _ = []

instance
    (ReflectableFields child1, ReflectableFields child2)
    => ReflectableFields (child1 Generics.:*: child2)
  where
    reflectStructFields (thing1 Generics.:*: thing2) =
        reflectStructFields thing1 ++ reflectStructFields thing2
    reflectProductValues (thing1 Generics.:*: thing2) =
        reflectProductValues thing1 ++ reflectProductValues thing2

instance
    (Datatype metadata, Reflectable' child)
    => Reflectable' (Generics.M1 Generics.D metadata child)
  where
    reflect' (Generics.M1 thing) = reflect' thing

instance
    (Constructor metadata, ReflectableFields child)
    => Reflectable' (Generics.M1 Generics.C metadata child)
  where
    reflect' m@(Generics.M1 thing) =
        if Generics.conIsRecord m
            then Fix
                (Struct ProductElement
                    { name = constructorName
                    , values= reflectStructFields thing
                    }
                )
            else mkSum constructorName (reflectProductValues thing)
      where
        constructorName =
            case Generics.conFixity m of
                Prefix -> Generics.conName m
                Infix _ _ -> "(" ++ Generics.conName m ++ ")"

instance (Reflectable' child1, Reflectable' child2)
    => Reflectable' (child1 Generics.:+: child2) where
    reflect' (Generics.L1 thing) = reflect' thing
    reflect' (Generics.R1 thing) = reflect' thing

instance Reflectable' Generics.V1 where
    reflect' a = case a of {}

----------------------------------
--      Utility functions       --
----------------------------------

-- TODO(virgil): Maybe use Data.Text.Prettyprint.Doc
{-| Crude attempt at representing some reflected data as it would look through
'show'.
-}
printData :: RecursiveData -> String
printData (Fix (Sum ProductElement {name, values = []})) =
    "(" ++ name ++ ")"
printData (Fix (Sum ProductElement {name, values})) =
    "(" ++ name ++ " " ++ unwords (map printData values) ++ ")"
printData (Fix (Struct ProductElement {name, values})) =
    name ++ " {" ++ intercalate "," (map printData values) ++ "}"
printData (Fix (StructField name value)) =
    name ++ "=" ++ printData value
printData (Fix (Value value)) =
    value
printData (Fix (List values)) =
    "[" ++ intercalate "," (map printData values) ++ "]"
printData (Fix (Tuple values)) =
    "(" ++ intercalate "," (map printData values) ++ ")"
printData (Fix Deleted) = ""

{-| Helper for creating a 'Sum' Data.
-}
mkSum :: String -> [RecursiveData] -> RecursiveData
mkSum name values =
    Fix (Sum ProductElement { name, values })

{-| Helper for creating a 'Struct' Data.
-}
mkStruct :: String -> [(String, RecursiveData)] -> RecursiveData
mkStruct structName values =
    mkRawStruct
        structName
        (map
            (\(fieldName, value) -> mkStructField fieldName value)
            values
        )

{-| Helper for creating a 'Struct' Data composed of things other than fields.
-}
mkRawStruct :: String -> [RecursiveData] -> RecursiveData
mkRawStruct structName values =
    Fix
        (Struct ProductElement
            { name = structName
            , values = values
            }
        )

{-| Helper for creating a 'StructField' RecursiveData.
-}
mkStructField :: String -> RecursiveData -> RecursiveData
mkStructField name value = Fix (StructField name value)

{-| Helper for creating a 'Value' RecursiveData.
-}
mkValue :: String -> RecursiveData
mkValue value1 = Fix (Value value1)

{-| Helper for creating a 'List' RecursiveData.
-}
mkList :: [RecursiveData] -> RecursiveData
mkList values = Fix (List values)

{-| Helper for creating a 'Tuple' RecursiveData.
-}
mkTuple :: [RecursiveData] -> RecursiveData
mkTuple values = Fix (Tuple values)

{-| Helper for creating a 'Deleted' RecursiveData.
-}
mkDeleted :: RecursiveData
mkDeleted = Fix Deleted
