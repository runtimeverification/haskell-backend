{-# LANGUAGE DeriveLift              #-}
{-# LANGUAGE NoDuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell         #-}

module VersionInfo
    ( VersionInfo (..)
    , versionInfo
    ) where

import Prelude.Kore

import Data.Aeson
    ( FromJSON
    )
import qualified Data.Aeson as Aeson
import qualified Development.GitRev as GitRev
import qualified GHC.Generics as GHC
import Language.Haskell.TH
    ( Exp
    , Q
    )
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax
    ( Lift
    )
import qualified Language.Haskell.TH.Syntax as TH
import qualified System.Directory as Directory
import System.FilePath
    ( takeDirectory
    , (</>)
    )

data VersionInfo =
    VersionInfo
    { gitHash :: !String
    , gitCommitDate :: !String
    , gitBranch :: !(Maybe String)
    , gitDirty :: !Bool
    }
    deriving stock (GHC.Generic)
    deriving stock (Lift)

instance FromJSON VersionInfo

versionInfo :: Q Exp
versionInfo = do
    packageRoot <- getPackageRoot
    let versionFile = packageRoot </> "version.json"
    haveVersionFile <- Directory.doesFileExist versionFile & TH.runIO
    if haveVersionFile
        then readVersionInfoFile versionFile
        else defaultVersionInfo
  where
    readVersionInfoFile versionFile = do
        result <- Aeson.eitherDecodeFileStrict' versionFile & TH.runIO
        either fail (TH.lift @_ @VersionInfo) result
    defaultVersionInfo =
        [| VersionInfo
            { gitHash = $(GitRev.gitHash)
            , gitCommitDate = $(GitRev.gitCommitDate)
            , gitBranch = Just $(GitRev.gitBranch)
            , gitDirty = $(GitRev.gitDirty)
            }
        |]

getPackageRoot :: Q FilePath
getPackageRoot = do
    bot <- takeDirectory . TH.loc_filename <$> TH.location
    TH.runIO $ findPackageRoot bot bot
  where
    isProjectRoot here = Directory.doesFileExist (here </> "package.yaml")

    -- Find the root directory of the current package. This module file can
    -- be moved safely because the package root is found at build time.
    findPackageRoot bot here
      | null here =
        fail ("Could not find package.yaml above " ++ bot)
      | otherwise = do
        foundRoot <- isProjectRoot here
        if foundRoot then Directory.makeAbsolute here else goUp
      where
        goUp = findPackageRoot bot (takeDirectory here)

