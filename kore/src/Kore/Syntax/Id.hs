{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause

Please refer to <http://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md kore-syntax.md>.
-}
module Kore.Syntax.Id (
    -- * InternedIdentifier
    InternedIdentifier (..),
    Intern.Description (..),

    -- * Identifiers
    Id (Id, getId, idLocation),
    getIdForError,
    noLocationId,
    implicitId,
    generatedId,

    -- * Locations
    AstLocation (..),
    FileLocation (..),
    prettyPrintAstLocation,
) where

import Control.Lens (
    lens,
 )
import Data.Generics.Product.Fields (
    HasField (..),
 )
import Data.Interned qualified as Intern
import Data.Interned.Internal.Text (
    InternedText (InternedText),
 )
import Data.String (
    IsString (..),
 )
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Kore.Unparser
import Prelude.Kore
import Pretty qualified

{- | 'InternedIdentifier' is a version of 'InternedText' with 'cacheWidth' equal to 1.

This ensures that the 'Array' of 'HashMap's, created with 'mkCache',
is going to be of length 1.
-}
newtype InternedIdentifier = InternedIdentifier
    { getInternedText :: InternedText
    }
    deriving newtype (Eq, Ord, Show, IsString, Hashable, Intern.Uninternable)
    deriving newtype (Debug, Diff)

instance Intern.Interned InternedIdentifier where
    type Uninterned InternedIdentifier = Text
    newtype Description InternedIdentifier = DII Text deriving stock (Eq)
    describe = DII
    identify iden txt = InternedIdentifier $ InternedText iden txt
    cacheWidth _ = 1
    cache = itCache

instance Hashable (Intern.Description InternedIdentifier) where
    hashWithSalt s (DII h) = hashWithSalt s h

itCache :: Intern.Cache InternedIdentifier
itCache = Intern.mkCache
{-# NOINLINE itCache #-}

{- | 'Id' is a Kore identifier.

'Id' corresponds to the @identifier@ syntactic category from <https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md#identifiers kore-syntax.md#identifiers>.
-}
data Id = InternedId
    { getInternedId :: !InternedIdentifier
    , internedIdLocation :: !AstLocation
    }
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

deriving stock instance GHC.Generic InternedText
deriving anyclass instance SOP.Generic InternedText
deriving anyclass instance SOP.HasDatatypeInfo InternedText
deriving anyclass instance NFData InternedText

deriving stock instance GHC.Generic InternedIdentifier
deriving anyclass instance SOP.Generic InternedIdentifier
deriving anyclass instance SOP.HasDatatypeInfo InternedIdentifier
deriving anyclass instance NFData InternedIdentifier

-- | Custom 'Show' instance matches the old uninterned Id interface.
instance Show Id where
    showsPrec = showsPrecId False

{- | Produces valid syntax for the 'Id' pattern synonym smart constructor.
   This hides the interning of the Text, including the transient unique
   integer value.
-}
instance Debug Id where
    debugPrec a = \p -> Pretty.pretty (showsPrecId True p a "")

{- | ShowS an 'Id' according to the old uninterned interface.

   If the 'Bool' is 'True', spaces are used between the braces and field
   names. Otherwise, no space is used.
-}
showsPrecId :: Bool -> Int -> Id -> ShowS
showsPrecId useSpace d (Id theId theLoc) = showParen (d > 10) showStr
  where
    showStr =
        showString "Id {" . space . showString "getId = "
            . shows theId
            . showString ", idLocation = "
            . shows theLoc
            . space
            . showChar '}'
    space
        | useSpace = showChar ' '
        | otherwise = id

{- | Debug instance hides the interning of InternedText.
   This is a good idea because we don't want to expose the transient value
   of the unique identifier for the interned value when creating syntax
   that could be fed back into GHCi. Instead, we want to produce comfortable
   syntax for the 'Id' pattern synonym, which uses raw text.
-}
instance Debug InternedText where
    debugPrec = debugPrec . Intern.unintern

-- | Diff instance hides the interning of InternedText. See the Debug instance.
instance Diff InternedText where
    diffPrec = diffPrec `on` Intern.unintern

{- | Pattern synonym smart constructor to intern the Text underlying an Id
   when created, and extract the interned Text when accessed.
-}
pattern Id :: Text -> AstLocation -> Id
pattern Id{getId, idLocation} <-
    InternedId (Intern.unintern -> getId) idLocation
    where
        Id txt loc = InternedId (Intern.intern txt) loc

{-# COMPLETE Id #-}

{- | HasField "idLocation" instance for the Id type maintains compatibility with
   the old interface of non-interned Ids.
-}
instance {-# OVERLAPPING #-} HasField "idLocation" Id Id AstLocation AstLocation where
    field = field @"internedIdLocation"

{- | HasField "getId" instance for the Id type maintains compatibility with
   the old interface of non-interned Ids.
-}
instance {-# OVERLAPPING #-} HasField "getId" Id Id Text Text where
    field = lens getId (\(Id _ a) txt' -> Id txt' a)

-- | 'Ord' ignores the 'AstLocation'
instance Ord Id where
    compare = compare `on` getInternedId

-- | 'Eq' ignores the 'AstLocation'
instance Eq Id where
    (==) = (==) `on` getInternedId
    {-# INLINE (==) #-}

-- | 'Hashable' ignores the 'AstLocation'
instance Hashable Id where
    hashWithSalt salt (InternedId text _) = hashWithSalt salt text
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
generatedId theId =
    -- Name punning doesn't work properly with pattern synonyms
    -- so we would get a warning here if we try to use it :(
    Id{getId = theId, idLocation = theLocation}
  where
    theLocation = AstLocationGeneratedVariable

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
