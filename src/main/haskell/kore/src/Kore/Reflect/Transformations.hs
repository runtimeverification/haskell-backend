{-|
Module      : Kore.Reflect.Transformations
Description : Concrete transformations for reflected Kore objects.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Reflect.Transformations
    (removeIdLocation
    ) where

import Kore.Reflect.Transform

{-| Deletes the idLocation field of an Id.
-}
removeIdLocation :: NodeTransformation
removeIdLocation =
    descend
        (Name "Id")
        (Transformation
            [delete (Name "idLocation")]
        )
