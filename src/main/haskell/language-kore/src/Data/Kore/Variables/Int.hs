{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Variables.Int ( IntVariable(..)
                                     ) where

import           Data.Kore.AST

class VariableClass var => IntVariable var where
    {-|Given an existing variable @v@ and an integer index @n@, 'intVariable'
    generates a "fresh" variable, whose name is based on index @n@, but
    which inherits the meta type and sort from @v@.
    -}
    intVariable :: IsMeta a => var a -> Int -> var a

instance IntVariable Variable where
    intVariable var n =
        var { variableName = Id (metaObjectPrefix ++ "var_" ++ show n) }
      where
        metaObjectPrefix = if isMeta var then "#" else ""
