{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Syntax.Module
    ( ModuleName (..)
    , getModuleNameForError
    , Module (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
    ( Hashable (..)
    )
import Data.Maybe
    ( catMaybes
    )
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Attributes
import Kore.Debug
import Kore.Unparser

{- | 'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: Text }
    deriving (Eq, GHC.Generic, IsString, Ord, Show)

instance Hashable ModuleName

instance NFData ModuleName

instance SOP.Generic ModuleName

instance SOP.HasDatatypeInfo ModuleName

instance Debug ModuleName

instance Diff ModuleName

instance Unparse ModuleName where
    unparse = Pretty.pretty . getModuleName
    unparse2 = Pretty.pretty . getModuleName


getModuleNameForError :: ModuleName -> String
getModuleNameForError = Text.unpack . getModuleName

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module (sentence :: *) =
    Module
        { moduleName       :: !ModuleName
        , moduleSentences  :: ![sentence]
        , moduleAttributes :: !Attributes
        }
    deriving (Eq, Functor, Foldable, GHC.Generic, Show, Traversable)

instance Hashable sentence => Hashable (Module sentence)

instance NFData sentence => NFData (Module sentence)

instance SOP.Generic (Module sentence)

instance SOP.HasDatatypeInfo (Module sentence)

instance Debug sentence => Debug (Module sentence)

instance (Debug sentence, Diff sentence) => Diff (Module sentence)

instance Unparse sentence => Unparse (Module sentence) where
    unparse
        Module { moduleName, moduleSentences, moduleAttributes }
      =
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
        Module { moduleName, moduleSentences, moduleAttributes }
      =
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
