{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Module (
    ModuleName (..),
    getModuleNameForError,
    Module (..),
) where

import Data.Kind (
    Type,
 )
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Attributes
import Kore.Debug
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- | 'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName {getModuleName :: Text}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving newtype (IsString)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse ModuleName where
    unparse = Pretty.pretty . getModuleName
    unparse2 = Pretty.pretty . getModuleName

getModuleNameForError :: ModuleName -> String
getModuleNameForError = Text.unpack . getModuleName

{- |A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module (sentence :: Type) = Module
    { moduleName :: !ModuleName
    , moduleSentences :: ![sentence]
    , moduleAttributes :: !Attributes
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Debug sentence => Debug (Module sentence)

instance (Debug sentence, Diff sentence) => Diff (Module sentence)

instance Unparse sentence => Unparse (Module sentence) where
    unparse
        Module{moduleName, moduleSentences, moduleAttributes} =
            (Pretty.vsep . catMaybes)
                [ Just ("module" Pretty.<+> unparse moduleName)
                , case moduleSentences of
                    [] -> Nothing
                    _ ->
                        (Just . Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> moduleSentences)
                , Just "endmodule"
                , Just (unparse moduleAttributes)
                ]

    unparse2
        Module{moduleName, moduleSentences, moduleAttributes} =
            (Pretty.vsep . catMaybes)
                [ Just ("module" Pretty.<+> unparse2 moduleName)
                , case moduleSentences of
                    [] -> Nothing
                    _ ->
                        (Just . Pretty.indent 4 . Pretty.vsep)
                            (unparse2 <$> moduleSentences)
                , Just "endmodule"
                , Just (unparse2 moduleAttributes)
                ]
