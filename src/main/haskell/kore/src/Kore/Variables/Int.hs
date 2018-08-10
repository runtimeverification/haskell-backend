{-|
Module      : Kore.Variables.Int
Description : Defines the 'IntVariable' class providing functionality for
              generating variables based on intergers.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Int
    ( IntVariable(..)
    ) where

import Kore.AST.Common
import Kore.AST.MetaOrObject

class IntVariable var where
    {-|Given an existing variable @v@ and an integer index @n@, 'intVariable'
    generates a "fresh" variable, whose name is based on index @n@, but
    which inherits the meta type and sort from @v@.
    -}
    intVariable :: MetaOrObject level => var level -> Int -> var level

instance IntVariable Variable where
    intVariable var n =
        var
            { variableName = Id
                { getId = metaObjectPrefix ++ "var_" ++ show n
                , idLocation = AstLocationGeneratedVariable
                }
            }
      where
        metaObjectPrefix =
            case isMetaOrObject var of
                IsObject -> ""
                IsMeta   -> "#"
