{-|
Module      : Kore.Attribute.RuleIndex
Description : Rule index attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : ???@runtimeverification.com

-}
module Kore.Attribute.RuleIndex
    ( RuleIndex (..)
    , ruleIndexId, ruleIndexSymbol, ruleIndexAttribute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @RuleIndex@ represents the @RuleIndex@ attribute.
 -}
newtype RuleIndex = RuleIndex { getRuleIndex :: Maybe Int }
    deriving (Eq, Ord, Show, Generic)

instance NFData RuleIndex

instance Default RuleIndex where
    def = RuleIndex Nothing

-- | Kore identifier representing the @ruleIndex@ attribute symbol.
ruleIndexId :: Id Object
ruleIndexId = "ruleIndex"

-- | Kore symbol representing the @ruleIndex@ attribute.
ruleIndexSymbol :: SymbolOrAlias Object
ruleIndexSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = ruleIndexId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @ruleIndex@ attribute.
ruleIndexAttribute :: CommonKorePattern
ruleIndexAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = ruleIndexSymbol
            , applicationChildren = []
            }

instance ParseAttributes RuleIndex where
    parseAttribute =
        withApplication $ \params args RuleIndex { getRuleIndex } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            return RuleIndex { getRuleIndex = Nothing }
      where
        withApplication = Parser.withApplication ruleIndexId
        failDuplicate = Parser.failDuplicate ruleIndexId
