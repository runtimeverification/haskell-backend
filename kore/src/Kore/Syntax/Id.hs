{-# LANGUAGE MagicHash #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause

Please refer to <http://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md kore-syntax.md>.
-}
module Kore.Syntax.Id (
    -- * Identifiers
    Id,
    getId,
    idLocation,
    getIdForError,
    noLocationId,
    implicitId,
    generatedId,
    locatedId,

    -- * Locations
    AstLocation (..),
    FileLocation (..),
    prettyPrintAstLocation,
) where

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.IORef
import Data.String (
    IsString (..),
 )
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import GHC.Exts (reallyUnsafePtrEquality#)
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Kore.Unparser
import Prelude.Kore
import Pretty qualified
import System.IO.Unsafe (unsafePerformIO)

{- | 'Id' is a Kore identifier.

'Id' corresponds to the @identifier@ syntactic category from <https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md#identifiers kore-syntax.md#identifiers>.
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
    compare (Id a _) (Id b _) = fastCmpText a b
    {-# INLINE compare #-}

-- | 'Eq' ignores the 'AstLocation'
instance Eq Id where
    Id a _ == Id b _ = fastEqText a b
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
noLocationId name = locatedId name AstLocationNone

-- | Create an implicit 'Id'.
implicitId :: Text -> Id
implicitId name = locatedId name AstLocationImplicit

{- | Create a generated 'Id'.

The location will be 'AstLocationGeneratedVariable'.
-}
generatedId :: Text -> Id
generatedId name = locatedId name AstLocationGeneratedVariable

-- | Create an 'Id' with the specified location.
locatedId :: Text -> AstLocation -> Id
locatedId s loc = Id (dedupText s) loc

fastCmpText :: Text -> Text -> Ordering
fastCmpText a b =
    case reallyUnsafePtrEquality# a b of
        1# -> EQ
        _ -> compare a b

fastEqText :: Text -> Text -> Bool
fastEqText a b =
    case reallyUnsafePtrEquality# a b of
        1# -> True
        _ -> a == b

{-# NOINLINE dedupText #-}
dedupText :: Text -> Text
dedupText s = unsafePerformIO $ do
    tbl0 <- readIORef textTable
    case HashMap.lookup s tbl0 of
        Just s' -> return s'
        Nothing -> do
            atomicModifyIORef textTable $ \tbl ->
                (HashMap.insert s s tbl, s)

{-# NOINLINE textTable #-}
textTable :: IORef (HashMap Text Text)
textTable = unsafePerformIO (newIORef HashMap.empty)

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
