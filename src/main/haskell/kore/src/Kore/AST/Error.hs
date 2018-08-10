{-|
Module      : Kore.AST.Error
Description : Extensions for errors related to the AST.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.AST.Error
    ( koreFailWithLocations
    , koreFailWithLocationsWhen
    , withLocationAndContext
    , withLocationsContext
    ) where

import Data.List
       ( intercalate )

import Kore.AST.AstWithLocation
import Kore.Error

{-|'koreFailWithLocations' produces an error result with a context containing
the provided locations. -}
koreFailWithLocations
    :: AstWithLocation astWithLocation
    => [astWithLocation] -> String -> Either (Error a) b
koreFailWithLocations locations errorMessage =
    withLocationsContext locations (koreFail errorMessage)

{-|'koreFailWithLocationsWhen' produces an error result with a context
containing the provided locations whenever the provided flag is true.
-}
koreFailWithLocationsWhen
    :: AstWithLocation astWithLocation
    => Bool -> [astWithLocation] -> String -> Either (Error a) ()
koreFailWithLocationsWhen condition locations errorMessage =
    withLocationsContext locations (koreFailWhen condition errorMessage)

{-|'withLocationsContext' prepends the given location to the error context
whenever the given action fails.
-}
withLocationsContext
    :: AstWithLocation astWithLocation
    => [astWithLocation] -> Either (Error a) result -> Either (Error a) result
withLocationsContext locations =
    withContext
        (  "("
        ++ intercalate ", " (map prettyPrintLocationFromAst locations)
        ++ ")"
        )

{-|'withLocationsContext' prepends the given message, associated with the
location, to the error context whenever the given action fails.
-}
withLocationAndContext
    :: AstWithLocation astWithLocation
    => astWithLocation
    -> String
    -> Either (Error a) result
    -> Either (Error a) result
withLocationAndContext location message =
    withContext (message ++ " (" ++ prettyPrintLocationFromAst location ++ ")")
