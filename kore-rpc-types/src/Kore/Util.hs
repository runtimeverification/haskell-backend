{- |
Copyright   : (c) Runtime Verification, 2019-2024
License     : BSD-3-Clause
-}
module Kore.Util (
    showHashHex,
    extractLogMessageContext,
) where

import Data.Char
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Word (Word64)
import Numeric (showHex)

-- | Represent an 'Int' as a short hexadecimal string
showHashHex :: Int -> Text
showHashHex h = let cutoff = 7 in Text.pack . take cutoff $ showHex (fromIntegral @Int @Word64 h) ""

-- | From a Kore/Booster contextual one-line log message, extract the context prefix
extractLogMessageContext :: Text -> Text
extractLogMessageContext = Text.filter (not . isBracket) . Text.takeWhile isContextCharacter
  where
    isContextCharacter :: Char -> Bool
    isContextCharacter c = isHexDigit c || isLower c || isSpace c || isBracket c

    isBracket = \case
        '[' -> True
        ']' -> True
        _ -> False
