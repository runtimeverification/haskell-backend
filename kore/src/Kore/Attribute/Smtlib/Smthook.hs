{- |
Module      : Kore.Attribute.Smtlib.Smtlib
Description : SMT-HOOK translation attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com

-}
module Kore.Attribute.Smtlib.Smthook
    ( Smthook (..)
    , smthookId
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
       ( Default (..) )
import GHC.Generics
       ( Generic )

import Kore.AST.Identifier
       ( Id )
import Kore.AST.MetaOrObject
       ( Object )
import SimpleSMT
       ( SExpr )

{- | The @smthook@ attribute for symbols.

The @smthook@ attribute allows a Kore symbol and its arguments to be translated
for an external SMT solver. @smthook@ is meant to be used similarly to how
@smtlib@ is used, with the exception that it is meant for encoding into
builtin operations provided by the SMT solver and, as such, the symbol
used for encoding needs not be declared.

See 'Kore.Attribute.Smtlib.Smtlib'

 -}
newtype Smthook = Smthook { getSmthook :: Maybe SExpr }
    deriving (Generic, Eq, Ord, Show)

instance Default Smthook where
    def = Smthook Nothing

instance NFData Smthook

-- | Kore identifier representing the @smthook@ attribute symbol.
smthookId :: Id Object
smthookId = "smt-hook"
