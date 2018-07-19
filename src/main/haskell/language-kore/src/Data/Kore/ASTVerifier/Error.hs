{-|
Module      : Data.Kore.ASTVerifier.Error
Description : Helpers for verification errors.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.Error where

import Data.Kore.Error

{-| 'VerifyError' is a tag for verification errors. -}
newtype VerifyError = VerifyError ()
    deriving (Eq, Show)
{-| 'VerifySuccess' is a tag for verification success. -}
newtype VerifySuccess = VerifySuccess ()
    deriving (Eq, Show)

{-| 'verifySuccess' helper for signaling verification success. -}
verifySuccess :: Either (Error VerifyError) VerifySuccess
verifySuccess = Right (VerifySuccess ())
