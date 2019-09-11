{-# LANGUAGE TemplateHaskell #-}

module Paths where

import qualified Language.Haskell.TH as TH
import System.Directory
    ( doesFileExist
    , makeAbsolute
    )
import System.FilePath
    ( takeDirectory
    , (</>)
    )


{-| Resolve the file name of a test resource relative to the package root.

The package root is the directory containing a `package.yaml` file. The source
tree used to build the test must remain unpacked. Any resources used must be
added to @extra-source-files@ in the package description.
-}
dataFileName :: FilePath -> FilePath
dataFileName relative =
    let
        packageRoot = $(do
            bot <- takeDirectory . TH.loc_filename <$> TH.location
            let
                isProjectRoot here = doesFileExist (here </> "package.yaml")
                {- Find the root directory of the current package. This module
                   file can be moved safely because the package root is found at
                   build time. -}
                findPackageRoot here
                    | null here =
                        fail ("Could not find package.yaml above " ++ bot)
                    | otherwise =
                        do
                            foundRoot <- TH.runIO $ isProjectRoot here
                            if foundRoot
                                then TH.runIO $ makeAbsolute here
                                else findPackageRoot (takeDirectory here)
            root <- findPackageRoot bot
            TH.litE (TH.stringL root)
            )
    in
        packageRoot </> relative
