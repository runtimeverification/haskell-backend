{-|
Module      : Kore.Attribute.Injective
Description : Injective symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Injective
    ( Injective (..)
    , injectiveId, injectiveSymbol, injectiveAttribute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @Injective@ represents the @injective@ attribute for symbols.
 -}
newtype Injective = Injective { isDeclaredInjective :: Bool }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Injective where
    (<>) (Injective a) (Injective b) = Injective (a || b)

instance Monoid Injective where
    mempty = Injective False

instance Default Injective where
    def = mempty

instance NFData Injective

-- | Kore identifier representing the @injective@ attribute symbol.
injectiveId :: Id Object
injectiveId = "injective"

-- | Kore symbol representing the @injective@ attribute.
injectiveSymbol :: SymbolOrAlias Object
injectiveSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = injectiveId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @injective@ attribute.
injectiveAttribute :: CommonKorePattern
injectiveAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = injectiveSymbol
            , applicationChildren = []
            }

instance ParseAttributes Injective where
    parseAttribute =
        withApplication parseApplication
      where
        parseApplication params args Injective { isDeclaredInjective } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isDeclaredInjective failDuplicate
            return Injective { isDeclaredInjective = True }
        withApplication = Parser.withApplication injectiveId
        failDuplicate = Parser.failDuplicate injectiveId
