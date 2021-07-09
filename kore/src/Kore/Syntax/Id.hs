{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.Syntax.Id (
    -- * Identifiers
    Id (..),
    getIdForError,
    noLocationId,
    implicitId,
    generatedId,

    -- * Locations
    AstLocation (..),
    FileLocation (..),
    prettyPrintAstLocation,
) where

import Data.String (
    IsString (..),
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- | @Id@ is a Kore identifier.

@Id@ corresponds to the @identifier@ syntactic category from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
data Id = Id
    { getId :: !Text
    , idLocation :: !AstLocation
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

-- | 'Ord' ignores the 'AstLocation'
instance Ord Id where
    compare first@(Id _ _) second@(Id _ _) =
        compare (getId first) (getId second)

-- | 'Eq' ignores the 'AstLocation'
instance Eq Id where
    first == second = compare first second == EQ
    {-# INLINE (==) #-}

-- | 'Hashable' ignores the 'AstLocation'
instance Hashable Id where
    hashWithSalt salt (Id text _) = hashWithSalt salt text
    {-# INLINE hashWithSalt #-}

instance Diff Id where
    diffPrec a b =
        diffPrecGeneric
            a{idLocation = AstLocationNone}
            b{idLocation = AstLocationNone}

instance IsString Id where
    fromString = noLocationId . fromString

instance Unparse Id where
    unparse = Pretty.pretty . getId
    unparse2 = Pretty.pretty . getId

{- | Create an 'Id' without location.

Before doing this, you should consider using an existing case or adding a new
constructor to 'AstLocation'.
-}
noLocationId :: Text -> Id
noLocationId name = Id name AstLocationNone

-- | Create an implicit 'Id'.
implicitId :: Text -> Id
implicitId name = Id name AstLocationImplicit

{- | Create a generated 'Id'.

The location will be 'AstLocationGeneratedVariable'.
-}
generatedId :: Text -> Id
generatedId getId =
    Id{getId, idLocation}
  where
    idLocation = AstLocationGeneratedVariable

-- | Get the identifier name for an error message 'String'.
getIdForError :: Id -> String
getIdForError = Text.unpack . getId

{- | 'AstLocation' represents the origin of an AST node.

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
    | AstLocationFile !FileLocation
    | -- | This should not be used and should be eliminated in further releases
      AstLocationUnknown
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

{- | 'prettyPrintAstLocation' displays an `AstLocation` in a way that's
(sort of) user friendly.
-}
prettyPrintAstLocation :: AstLocation -> Text
prettyPrintAstLocation AstLocationNone = "<unknown location>"
prettyPrintAstLocation AstLocationImplicit = "<implicitly defined entity>"
prettyPrintAstLocation AstLocationGeneratedVariable =
    "<variable generated internally>"
prettyPrintAstLocation AstLocationTest = "<test data>"
prettyPrintAstLocation
    ( AstLocationFile
            FileLocation
                { fileName = name
                , line = line'
                , column = column'
                }
        ) =
        Text.pack name <> " "
            <> Text.pack (show line')
            <> ":"
            <> Text.pack (show column')
prettyPrintAstLocation AstLocationUnknown = "<unknown location>"

-- | 'FileLocation' represents a position in a source file.
data FileLocation = FileLocation
    { fileName :: !FilePath
    , line :: !Int
    , column :: !Int
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
