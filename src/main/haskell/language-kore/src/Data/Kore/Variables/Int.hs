{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Kore.Variables.Int
    ( IntVariable(..)
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject

class IntVariable var
    {-|Given an existing variable @v@ and an integer index @n@, 'intVariable'
    generates a "fresh" variable, whose name is based on index @n@, but
    which inherits the meta type and sort from @v@.
    -}
  where
    intVariable :: MetaOrObject level => var level -> Int -> var level

instance IntVariable Variable where
    intVariable var n =
        var { variableName = Id (metaObjectPrefix ++ "var_" ++ show n) }
      where
        metaObjectPrefix =
            applyMetaObjectFunction
                var
                MetaOrObjectTransformer
                    { objectTransformer = const ""
                    , metaTransformer = const "#"
                    }
