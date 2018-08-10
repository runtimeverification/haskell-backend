{-|
Module      : Logic.Matching.Error
Description : Helpers for errors related to matching logic
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Logic.Matching.Error where

import Data.Text.Prettyprint.Doc

import Kore.Error

{-| 'MLError' is a tag for errors related to matching logic. -}
newtype MLError = MLError ()
    deriving (Eq, Show)

{-| 'MLSuccess' is a tag for success related to matching logic. -}
newtype MLSuccess = MLSuccess ()
    deriving (Eq, Show)

{-| 'mlSuccess' helper for signaling success related to matching logic. -}
mlSuccess :: Either (Error MLError) MLSuccess
mlSuccess = Right (MLSuccess ())

mlFailWhen :: Bool -> [Doc ann] -> Either (Error a) ()
mlFailWhen condition docs =
    koreFailWhen condition (show (concatWith (<>) docs))

mlFail :: [Doc ann] -> Either (Error a) b
mlFail docs =
    koreFail (show (concatWith (<>) docs))
