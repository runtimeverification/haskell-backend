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
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import Kore.Error
import Kore.Sort
import Kore.Unparser

{-| 'VerifyError' is a tag for verification errors. -}
newtype VerifyError = VerifyError ()
    deriving (Eq, Show)
{-| 'VerifySuccess' is a tag for verification success. -}
newtype VerifySuccess = VerifySuccess ()
    deriving (Eq, Show)

{-| 'verifySuccess' helper for signaling verification success. -}
verifySuccess :: MonadError (Error VerifyError) m => m VerifySuccess
verifySuccess = return (VerifySuccess ())

noConstructorWithDomainValues :: Id -> Sort -> String
noConstructorWithDomainValues symbolId sort =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , Pretty.squotes (unparse symbolId)
        , "for sort"
        , Pretty.squotes (unparse sort) <> Pretty.colon
        , "sort has domain values."
        ]

noConstructorInHookedSort :: Id -> Sort -> String
noConstructorInHookedSort symbolId sort =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , Pretty.squotes (unparse symbolId)
        , "for hooked sort"
        , Pretty.squotes (unparse sort) <> Pretty.dot
        ]

noConstructorWithVariableSort :: Id -> String
noConstructorWithVariableSort symbolId =
    (show . Pretty.hsep)
        [ "Cannot define constructor"
        , Pretty.squotes (unparse symbolId)
        , "with variable result sort."
        ]

sortNeedsDomainValueAttributeMessage :: Text
sortNeedsDomainValueAttributeMessage =
    "Sorts used with domain value must have the '"
    <> getId Attribute.HasDomainValues.hasDomainValuesId
    <> "' " <> "attribute."
