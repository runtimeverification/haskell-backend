{-# LANGUAGE BlockArguments #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause

Please refer to <http://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md kore-syntax.md>.
-}
module Kore.Syntax.Id (
    -- * Identifiers
    Id (..),
    pattern Id,
    getId,
    idLocation,
    getIdForError,
    noLocationId,
    implicitId,
    generatedId,
    globalIdMap,
    InternedTextCache (..),

    -- * Locations
    AstLocation (..),
    FileLocation (..),
    prettyPrintAstLocation,
) where

import Control.Lens (lens)
import Data.Generics.Product
import Data.HashMap.Strict as HashMap
import Data.IORef
import Data.String (
    IsString (..),
 )
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import GHC.Generics (Generic)
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Kore.Unparser
import Prelude.Kore
import Pretty qualified
import System.IO.Unsafe (unsafePerformIO)

data InternedTextCache = InternedTextCache
    { counter :: {-# UNPACK #-} !Int
    , internedTexts :: !(HashMap Text Int)
    }
    deriving stock (Generic)
    deriving anyclass (NFData)

globalIdMap :: IORef InternedTextCache
globalIdMap = unsafePerformIO $ newIORef $ InternedTextCache 0 HashMap.empty
{-# NOINLINE globalIdMap #-}

data InternedText = InternedText
    { getText :: {-# UNPACK #-} !Text
    , getUniqueId :: {-# UNPACK #-} !Int
    }
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Show InternedText where
    showsPrec prec = showsPrec prec . getText

instance Debug InternedText where
    debugPrec = debugPrec . getText

instance Diff InternedText where
    diffPrec = diffPrec `on` getText

internText :: Text -> InternedText
internText text =
    unsafePerformIO do
        atomicModifyIORef' globalIdMap \InternedTextCache{counter, internedTexts} ->
            let ((internedText, newCounter), newInternedTexts) =
                    HashMap.alterF
                        \case
                            -- If this text is already interned, reuse it.
                            existing@(Just iden) -> ((InternedText text iden, counter), existing)
                            -- Otherwise, create a new ID for it and intern it.
                            Nothing ->
                                let newIden = counter
                                 in ((InternedText text newIden, counter + 1), Just newIden)
                        text
                        internedTexts
             in (InternedTextCache newCounter newInternedTexts, internedText)

{- | 'Id' is a Kore identifier.

'Id' corresponds to the @identifier@ syntactic category from <https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md#identifiers kore-syntax.md#identifiers>.
-}
data Id = InternedId
    { getInternedId :: !InternedText
    , internedIdLocation :: !AstLocation
    }
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

pattern Id :: Text -> AstLocation -> Id
pattern Id{getId, idLocation} <-
    InternedId (getText -> getId) idLocation
    where
        Id text location = InternedId (internText text) location

{-# COMPLETE Id #-}

instance Show Id where
    showsPrec = showsPrecId False

{- | Produces valid syntax for the 'Id' pattern synonym.
   This hides the interning of the Text, including the unique identifier.
-}
instance Debug Id where
    debugPrec a prec = Pretty.pretty (showsPrecId True prec a "")

{- | ShowS an 'Id' in accordance with the old uninterned interface.
   If the predicate 'useSpace' is 'True', spaces are placed between the braces and the field
   names.
-}
showsPrecId :: Bool -> Int -> Id -> ShowS
showsPrecId useSpace prec (Id iden location) = showParen (prec > 10) showId
  where
    showId =
        showString "Id {"
            . space
            . showString "getId = "
            . shows iden
            . showString ", idLocation = "
            . shows location
            . space
            . showChar '}'
    space
        | useSpace = showChar ' '
        | otherwise = id

{- | The @HasField "getId"@ instance for the Id type maintains compatibility with
   the old interface of non-interned Ids.
-}
instance {-# OVERLAPPING #-} HasField "getId" Id Id Text Text where
    field = lens getId (\(Id _ iden) text -> Id text iden)

{- | The @HasField "idLocation"@ instance for the Id type maintains compatibility with
   the old interface of non-interned Ids.
-}
instance {-# OVERLAPPING #-} HasField "idLocation" Id Id AstLocation AstLocation where
    field = field @"internedIdLocation"

-- | 'Ord' ignores the 'AstLocation'
instance Ord Id where
    a `compare` b
        -- Quickly check if their interned IDs are equal.
        | a == b = EQ
        -- If they're not, fallback to using lexical order by comparing the strings' actual contents.
        | otherwise = getId a `compare` getId b
    {-# INLINE compare #-}

-- | 'Eq' ignores the 'AstLocation'
instance Eq Id where
    first == second = getUniqueId (getInternedId first) == getUniqueId (getInternedId second)
    {-# INLINE (==) #-}

-- | 'Hashable' ignores the 'AstLocation'
instance Hashable Id where
    hashWithSalt salt internedId = hashWithSalt salt $ getUniqueId (getInternedId internedId)
    {-# INLINE hashWithSalt #-}
    hash internedId = hash $ getUniqueId (getInternedId internedId)
    {-# INLINE hash #-}

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
generatedId text =
    Id{getId = text, idLocation = location}
  where
    location = AstLocationGeneratedVariable

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
