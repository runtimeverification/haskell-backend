module Data.Kore.ASTVerifier.Error where

import Data.Kore.Error

newtype VerifyError = VerifyError ()
    deriving (Eq, Show)
newtype VerifySuccess = VerifySuccess ()
    deriving (Eq, Show)

verifySuccess :: Either (Error VerifyError) VerifySuccess
verifySuccess = Right (VerifySuccess ())
