{- |
Module      : Kore.Attribute.Smtlib.Smtlib
Description : SMT-LIB translation attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Smtlib.Smtlib
    ( Smtlib (..)
    , smtlibId
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

{- | The @smtlib@ attribute for symbols.

The @smtlib@ attribute allows a Kore symbol and its arguments to be translated
for an external SMT solver.

Kore syntax: @smtlib{}(\"≪S-expression≫\")@, where @≪S-expression≫@ is an
S-expression defined by the SMT-LIB 2 standard. If @≪S-expression≫@ is an atom,
that atom is used as the head of a list expression and all the arguments of the
hooked Kore symbol are passed as arguments of the list. If @≪S-expression≫@ is a
list, that list is passed to the SMT solver; in this case, the special
meta-variable symbols @#≪n≫@ (where @≪n≫@ is a positive integer) are replaced by
the positional parameters of the hooked Kore symbol. Note that the
meta-variable symbols are only valid in the @smtlib@ attribute; they are /not/
valid SMT-LIB S-expressions.

 -}
newtype Smtlib = Smtlib { getSmtlib :: Maybe SExpr }
    deriving (Generic, Eq, Ord, Show)

instance Default Smtlib where
    def = Smtlib Nothing

instance NFData Smtlib

-- | Kore identifier representing the @smtlib@ attribute symbol.
smtlibId :: Id Object
smtlibId = "smtlib"
