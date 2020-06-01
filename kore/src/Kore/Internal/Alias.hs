{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Alias
    ( Alias (..)
    , toSymbolOrAlias
    -- * Re-exports
    , module Kore.Internal.ApplicationSorts
    ) where

import Prelude.Kore

import Control.DeepSeq
import qualified Data.Foldable as Foldable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.AST.AstWithLocation
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.ApplicationSorts
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Variable
    ( VariableName
    )
import Kore.Unparser
import Kore.Variables.UnifiedVariable

data Alias patternType =
    Alias
        { aliasConstructor :: !Id
        , aliasParams      :: ![Sort]
        , aliasSorts       :: !ApplicationSorts
        , aliasLeft        :: [SomeVariable VariableName]
        , aliasRight       :: patternType
        }
    deriving (GHC.Generic, Show)

instance Eq patternType => Eq (Alias patternType) where
    (==) a b =
            on (==) aliasConstructor a b
        &&  on (==) aliasParams a b
    {-# INLINE (==) #-}

instance Ord patternType => Ord (Alias patternType) where
    compare a b =
            on compare aliasConstructor a b
        <>  on compare aliasParams a b

instance Hashable patternType => Hashable (Alias patternType) where
    hashWithSalt salt Alias { aliasConstructor, aliasParams } =
        salt `hashWithSalt` aliasConstructor `hashWithSalt` aliasParams

instance NFData patternType => NFData (Alias patternType)

instance SOP.Generic (Alias patternType)

instance SOP.HasDatatypeInfo (Alias patternType)

instance Debug patternType => Debug (Alias patternType)

instance (Debug patternType, Diff patternType) => Diff (Alias patternType)

instance Unparse (Alias patternType) where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor
        <> parameters aliasParams

    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Application (Alias patternType))
  where
    -- TODO (thomas.tuegel): Consider that there could be bound variables here.
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Application (Alias patternType)) where
    synthetic application =
        resultSort & deepseq (matchSorts operandSorts children)
      where
        Application { applicationSymbolOrAlias = alias } = application
        Application { applicationChildren = children } = application
        Alias { aliasSorts } = alias
        resultSort = applicationSortsResult aliasSorts
        operandSorts = applicationSortsOperands aliasSorts

instance AstWithLocation (Alias patternType) where
    locationFromAst = locationFromAst . aliasConstructor

toSymbolOrAlias :: Alias patternType -> SymbolOrAlias
toSymbolOrAlias alias =
    SymbolOrAlias
        { symbolOrAliasConstructor = aliasConstructor alias
        , symbolOrAliasParams = aliasParams alias
        }
