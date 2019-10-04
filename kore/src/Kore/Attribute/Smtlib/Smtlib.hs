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
    , smtlibSymbol
    , smtlibAttribute
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Default
    ( Default (..)
    )
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Attributes
import Kore.Debug
import Kore.Syntax.Application
    ( SymbolOrAlias (..)
    )
import Kore.Syntax.Id
    ( Id
    )
import SMT.SimpleSMT
    ( SExpr
    )

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
    deriving (GHC.Generic, Eq, Ord, Show)

instance Default Smtlib where
    def = Smtlib Nothing

instance NFData Smtlib

instance SOP.Generic Smtlib

instance SOP.HasDatatypeInfo Smtlib

instance Debug Smtlib

instance Diff Smtlib

-- | Kore identifier representing the @smtlib@ attribute symbol.
smtlibId :: Id
smtlibId = "smtlib"

-- | Kore symbol representing the @smtlib@ attribute.
smtlibSymbol :: SymbolOrAlias
smtlibSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = smtlibId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @smtlib@ attribute.
smtlibAttribute :: Text -> AttributePattern
smtlibAttribute syntax =
    attributePattern smtlibSymbol [attributeString syntax]
