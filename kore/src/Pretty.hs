{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Pretty
    ( module Data.Text.Prettyprint.Doc
    , layoutOneLine
    , renderText
    ) where

import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
    ( renderStrict
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
    worker (SLine _ stream)        = SChar ' ' (worker stream)

    worker SFail                   = SFail
    worker SEmpty                  = SEmpty
    worker (SChar char stream)     = SChar char (worker stream)
    worker (SText len text stream) = SText len text (worker stream)
    worker (SAnnPush ann stream)   = SAnnPush ann (worker stream)
    worker (SAnnPop stream)        = SAnnPop (worker stream)

renderText :: SimpleDocStream ann -> Text
renderText = renderStrict
