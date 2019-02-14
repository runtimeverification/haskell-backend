{- |
Module      : Kore.AST.Identifier
Description : Kore identifiers and locations
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.AST.Identifier
    (
    -- * Identifiers
      Id (..)
    , getIdForError
    , noLocationId
    -- * Locations
    , AstLocation (..)
    , FileLocation (..)
    , prettyPrintAstLocation
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
                 ( Hashable )
import           Data.String
                 ( IsString (..) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Unparser

{-| 'FileLocation' represents a position in a source file.
-}
data FileLocation = FileLocation
    { fileName :: FilePath
    , line     :: Int
    , column   :: Int
    }
    deriving (Eq, Show, Generic)

instance Hashable FileLocation
instance NFData FileLocation

{-| 'AstLocation' represents the origin of an AST node.

Its representation may change, e.g. the `AstLocationFile` branch could become a
range instead of a single character position. You should treat the entire
AstLocation as much as possible as an opaque token, i.e. hopefully only
the kore parsing code and pretty printing code below would access
the AstLocationFile branch.
-}
data AstLocation
    = AstLocationNone
    | AstLocationImplicit
    | AstLocationGeneratedVariable
    | AstLocationTest
    | AstLocationFile FileLocation
    | AstLocationLifted AstLocation
    | AstLocationUnknown
    -- ^ This should not be used and should be eliminated in further releases
    deriving (Eq, Show, Generic)

instance Hashable AstLocation
instance NFData AstLocation

{-| 'prettyPrintAstLocation' displays an `AstLocation` in a way that's
(sort of) user friendly.
-}
prettyPrintAstLocation :: AstLocation -> String
prettyPrintAstLocation AstLocationNone = "<unknown location>"
prettyPrintAstLocation AstLocationImplicit = "<implicitly defined entity>"
prettyPrintAstLocation AstLocationGeneratedVariable =
    "<variable generated internally>"
prettyPrintAstLocation AstLocationTest = "<test data>"
prettyPrintAstLocation
    (AstLocationFile FileLocation
        { fileName = name
        , line = line'
        , column = column'
        }
    )
    = name ++ " " ++ show line' ++ ":" ++ show column'
prettyPrintAstLocation (AstLocationLifted location) =
    "<lifted(" ++ prettyPrintAstLocation location ++ ")>"
prettyPrintAstLocation AstLocationUnknown = "<unknown location>"

{-|'Id' corresponds to the @object-identifier@ and @meta-identifier@
syntactic categories from the Semantics of K, Section 9.1.1 (Lexicon).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

We may chage the Id's representation in the future so one should treat it as
an opaque entity as much as possible.

Note that Id comparison ignores the AstLocation.
-}
data Id level = Id
    { getId      :: !Text
    , idLocation :: !AstLocation
    }
    deriving (Show, Generic)

instance Ord (Id level) where
    compare first@(Id _ _) second@(Id _ _) =
        compare (getId first) (getId second)

{-# ANN module ("HLint: ignore Redundant compare" :: String) #-}
instance Eq (Id level) where
    first == second = compare first second == EQ

instance Hashable (Id level)

instance NFData (Id level)

instance IsString (Id level) where
    fromString = noLocationId . fromString

instance Unparse (Id level) where
    unparse = Pretty.pretty . getId

{-| 'noLocationId' creates an Id without a source location. While there are some
narrow cases where this makes sense, you should really consider other options
(including adding a new entry to the `AstLocation` data definition).
-}
noLocationId :: Text -> Id level
noLocationId value = Id
    { getId = value
    , idLocation = AstLocationNone
    }

getIdForError :: Id level -> String
getIdForError = Text.unpack . getId
