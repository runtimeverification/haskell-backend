{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Pretty (
    module Prettyprinter,
    layoutOneLine,
    renderText,
    renderString,
    renderIO,
    hPutDoc,
    putDoc,
    prettyException,
) where

import Control.Exception (
    Exception,
    displayException,
 )
import Data.String (
    fromString,
 )
import Data.Text (
    Text,
 )
import Prelude.Kore
import Prettyprinter
import Prettyprinter.Render.String (
    renderString,
 )
import Prettyprinter.Render.Text (
    hPutDoc,
    putDoc,
    renderIO,
    renderStrict,
 )

{- | Lay out the document with no (automatic) line breaks.

Hard line breaks will be preserved, but soft line breaks are converted to
spaces.
-}
layoutOneLine :: Doc ann -> SimpleDocStream ann
layoutOneLine = flattenSimpleDocStream . layoutCompact

flattenSimpleDocStream :: SimpleDocStream ann -> SimpleDocStream ann
flattenSimpleDocStream = worker
  where
    worker (SLine _ stream) = SChar ' ' (worker stream)
    worker SFail = SFail
    worker SEmpty = SEmpty
    worker (SChar char stream) = SChar char (worker stream)
    worker (SText len text stream) = SText len text (worker stream)
    worker (SAnnPush ann stream) = SAnnPush ann (worker stream)
    worker (SAnnPop stream) = SAnnPop (worker stream)

renderText :: SimpleDocStream ann -> Text
renderText = renderStrict

-- | Display an 'Exception' nicely for the user.
prettyException :: Exception exn => exn -> Doc ann
prettyException = vsep . map fromString . lines . displayException
