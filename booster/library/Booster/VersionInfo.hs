{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoDuplicateRecordFields #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.VersionInfo (
    VersionInfo (..),
    versionInfo,
) where

import Data.Aeson (
    FromJSON,
 )
import Development.GitRev qualified as GitRev
import GHC.Generics qualified as GHC
import Language.Haskell.TH (
    Exp,
    Q,
 )
import Language.Haskell.TH.Syntax (
    Lift,
 )

-- | Information about the current version of the Haskell backend.
data VersionInfo = VersionInfo
    { gitHash :: !String
    , gitCommitDate :: !String
    , gitBranch :: !(Maybe String)
    , gitDirty :: !Bool
    }
    deriving stock (GHC.Generic)
    deriving stock (Lift)

instance FromJSON VersionInfo

-- | Produce (at compile-time) information about the current version of the Haskell backend.
versionInfo :: Q Exp
versionInfo =
    [|
        VersionInfo
            { gitHash = $(GitRev.gitHash)
            , gitCommitDate = $(GitRev.gitCommitDate)
            , gitBranch = Just $(GitRev.gitBranch)
            , gitDirty = $(GitRev.gitDirty)
            }
        |]
