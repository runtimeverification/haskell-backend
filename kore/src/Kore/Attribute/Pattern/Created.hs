{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Created
    ( Created (..)
    , hasKnownCreator
    ) where

import Control.DeepSeq
import Data.Hashable
    ( Hashable (hashWithSalt)
    )
import qualified Data.Maybe as Maybe
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import GHC.Generics
import GHC.Stack
    ( SrcLoc (..)
    )
import qualified GHC.Stack as GHC

import Kore.Attribute.Synthetic
import Kore.Debug

-- | 'Created' is used for debugging patterns, specifically for finding out
-- where a pattern was created. This is a field in the attributes of a pattern,
-- and it will default to 'Nothing'. This field is populated via the smart
-- constructors in 'Kore.Internal.TermLike'.
newtype Created = Created { getCreated :: Maybe GHC.CallStack }
    deriving (Generic, Show)

hasKnownCreator :: Created -> Bool
hasKnownCreator = Maybe.isJust . getCallStackHead

instance Eq Created where
    (==) _ _ = True

instance SOP.Generic Created

instance SOP.HasDatatypeInfo Created

instance NFData Created

instance Hashable Created where
    hashWithSalt _ _ = 0

instance Debug Created

instance Diff Created where
    diffPrec = diffPrecIgnore

instance Pretty Created where
    pretty =
        maybe "" go . getCallStackHead
      where
        go (name, loc) =
            Pretty.hsep
                [ "/* Created by"
                , Pretty.angles $ Pretty.pretty name
                , "at"
                , prettySrcLoc loc
                , "*/"
                ]

getCallStackHead :: Created -> Maybe (String, SrcLoc)
getCallStackHead Created { getCreated } =
    GHC.getCallStack <$> getCreated >>= Maybe.listToMaybe

prettySrcLoc :: SrcLoc -> Doc ann
prettySrcLoc srcLoc =
    mconcat
        [ Pretty.pretty srcLocFile
        , Pretty.colon
        , Pretty.pretty srcLocStartLine
        , Pretty.colon
        , Pretty.pretty srcLocStartCol
        ]
  where
    SrcLoc { srcLocFile, srcLocStartLine, srcLocStartCol } = srcLoc

instance Functor pat => Synthetic Created pat where
    synthetic = const (Created Nothing)
