{-|
Module      : Kore.ASTVerifier.Error
Description : Helpers for verification errors.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.Error where

import Data.Text
  ( Text
    )
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import Kore.Error
import Kore.Sort
  ( Sort,
    getSortId
    )
import Kore.Syntax.Id
  ( Id (getId),
    getIdForError
    )

{-| 'VerifyError' is a tag for verification errors. -}
newtype VerifyError = VerifyError ()
  deriving (Eq, Show)

{-| 'VerifySuccess' is a tag for verification success. -}
newtype VerifySuccess = VerifySuccess ()
  deriving (Eq, Show)

{-| 'verifySuccess' helper for signaling verification success. -}
verifySuccess :: MonadError (Error VerifyError) m => m VerifySuccess
verifySuccess = return (VerifySuccess ())

noConstructorWithDomainValuesMessage :: Id -> Sort -> String
noConstructorWithDomainValuesMessage symbol resultSort =
  "Cannot define constructor '" ++ getIdForError symbol
    ++ "' for sort with domain values '"
    ++ getIdForError (getSortId resultSort)
    ++ "'."

sortNeedsDomainValueAttributeMessage :: Text
sortNeedsDomainValueAttributeMessage =
  "Sorts used with domain value must have the '"
    <> getId Attribute.HasDomainValues.hasDomainValuesId
    <> "' "
    <> "attribute."
