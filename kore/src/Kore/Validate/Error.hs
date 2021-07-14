{- |
Module      : Kore.Validate.Error
Description : Helpers for verification errors.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Validate.Error (
    VerifyError (..),
    VerifySuccess (..),
    verifySuccess,
    sortNeedsDomainValueAttributeMessage,
    noConstructorWithVariableSort,
    noConstructorInHookedSort,
    noConstructorWithDomainValues,
) where

import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import Kore.Error
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

-- | 'VerifyError' is a tag for verification errors.
newtype VerifyError = VerifyError ()
    deriving stock (Eq, Show)

-- | 'VerifySuccess' is a tag for verification success.
newtype VerifySuccess = VerifySuccess ()
    deriving stock (Eq, Show)

-- | 'verifySuccess' helper for signaling verification success.
verifySuccess :: MonadError (Error VerifyError) m => m VerifySuccess
verifySuccess = return (VerifySuccess ())

noConstructorWithDomainValues :: Id -> Sort -> String
noConstructorWithDomainValues symbolId sort =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , unparse symbolId
        , "for sort"
        , unparse sort <> Pretty.colon
        , "sort has domain values."
        ]

noConstructorInHookedSort :: Id -> Sort -> String
noConstructorInHookedSort symbolId sort =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , unparse symbolId
        , "for hooked sort"
        , unparse sort <> Pretty.dot
        ]

noConstructorWithVariableSort :: Id -> String
noConstructorWithVariableSort symbolId =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , unparse symbolId
        , "with variable result sort."
        ]

sortNeedsDomainValueAttributeMessage :: Text
sortNeedsDomainValueAttributeMessage =
    "Sorts used with domain value must have the "
        <> getId Attribute.HasDomainValues.hasDomainValuesId
        <> " "
        <> "attribute."
