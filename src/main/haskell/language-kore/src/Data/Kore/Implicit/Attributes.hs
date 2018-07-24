{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-|
Module      : Data.Kore.Implicit.Attributes
Description : Haskell definitions for the implicit constructs for attributes.
              uncheckedAttributesModule gathers all of them in a Kore morule
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.Attributes
    ( attributeObjectSort
    , uncheckedAttributesModule
    , KeyValueAttribute (..)
    , attributeToKeyValueAttribute
    , ImplicitAttributes
    , keyOnlyAttribute
    , keyValueAttribute
    ) where

import           Data.Default

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTUtils.SmartPatterns


data KeyValueAttribute =
    KeyValueAttribute
    { key   :: String
    , value :: Maybe String
    }
  deriving (Show, Eq)

data ImplicitAttributes =
    ImplicitAttributes
    {
    }
  deriving (Show, Eq)

instance Default ImplicitAttributes where
    def = ImplicitAttributes {}


noParameterObjectSortAndSentence
    :: String -> (AstLocation -> Sort Object, KoreSentence)
noParameterObjectSortAndSentence name =
    ( \location -> SortActualSort SortActual
        { sortActualName = Id name location
        , sortActualSorts = []
        }
    , asSentence
        (SentenceSort
            { sentenceSortName       = Id name AstLocationImplicit
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
        :: KoreSentenceSort
        )
    )

{-| 'attributeObjectSort' is the sort for all top-level attribute patterns
-}
attributeObjectSort :: AstLocation -> Sort Object
attributeObjectSortSentence :: KoreSentence
(attributeObjectSort, attributeObjectSortSentence) =
    noParameterObjectSortAndSentence "Attribute"

{-| 'attributeKeyObjectSort' is the sort for attribute values
-}
attributeKeyObjectSort :: AstLocation -> Sort Object
attributeKeyObjectSortSentence :: KoreSentence
(attributeKeyObjectSort, attributeKeyObjectSortSentence) =
    noParameterObjectSortAndSentence "AttributeKey"

{-| 'attributeValueObjectSort' is the sort for attribute values
-}
attributeValueObjectSort :: AstLocation -> Sort Object
attributeValueObjectSortSentence :: KoreSentence
(attributeValueObjectSort, attributeValueObjectSortSentence) =
    noParameterObjectSortAndSentence "AttributeValue"

keyValueAttributeLabel :: String
keyValueAttributeLabel = "keyValueAttribute"

keyOnlyAttributeLabel :: String
keyOnlyAttributeLabel = "keyOnlyAttribute"

keyValueAttributeObjectSymbolSentence :: KoreSentence
keyValueAttributeObjectSymbolSentence =
    attributeObjectSymbolSentence keyValueAttributeLabel
        [attributeKeyObjectSort, attributeValueObjectSort]

keyOnlyAttributeObjectSymbolSentence :: KoreSentence
keyOnlyAttributeObjectSymbolSentence =
    attributeObjectSymbolSentence keyOnlyAttributeLabel [attributeKeyObjectSort]

implicitGroundHead :: String -> SymbolOrAlias level
implicitGroundHead = (`groundHead` AstLocationImplicit)

attributeToKeyValueAttribute :: CommonKorePattern -> Maybe KeyValueAttribute
attributeToKeyValueAttribute p =
    case patternKoreToPure Object p of
        Right (App_ h children)
          | h == implicitGroundHead keyValueAttributeLabel ->
                case children of
                    [~ (DV_ _ (StringLiteral_ k)), ~ (DV_ _ (StringLiteral_ v))]
                        -> Just KeyValueAttribute
                            { key = k
                            , value = Just v
                            }
                    _ -> Nothing
          |  h == implicitGroundHead keyOnlyAttributeLabel ->
                case children of
                    [~ (DV_ _ (StringLiteral_ k))] ->
                        Just KeyValueAttribute
                        { key = k
                        , value = Nothing
                        }
                    _ -> Nothing
           | otherwise -> Nothing
        _ -> Nothing

keyOnlyAttribute :: String -> CommonKorePattern
keyOnlyAttribute k = patternPureToKore
    (App_ (implicitGroundHead keyOnlyAttributeLabel)
        [DV_ (attributeKeyObjectSort AstLocationImplicit) (StringLiteral_ k)]
    )

keyValueAttribute :: String -> String -> CommonKorePattern
keyValueAttribute k v = patternPureToKore
    (App_ (implicitGroundHead keyValueAttributeLabel)
        [ DV_ (attributeKeyObjectSort AstLocationImplicit) (StringLiteral_ k)
        , DV_ (attributeValueObjectSort AstLocationImplicit) (StringLiteral_ v)
        ]
    )

attributeObjectSymbolSentence
  :: String                       -- ^ attribute symbol
  -> [AstLocation -> Sort Object] -- ^ argument sort constructor
  -> KoreSentence
attributeObjectSymbolSentence name sorts =
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol  = Symbol
                { symbolConstructor = Id name AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = sorts <*> pure AstLocationImplicit
            , sentenceSymbolResultSort = attributeObjectSort AstLocationImplicit
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object
        )

{-| 'uncheckedAttributesModule' contains declarations for all symbols visible
in attributes;
-}
uncheckedAttributesModule :: KoreModule
uncheckedAttributesModule =
    Module
        { moduleName       = ModuleName "BUILTIN-attributes"
        , moduleSentences  =
            [ attributeObjectSortSentence
            , attributeKeyObjectSortSentence
            , attributeValueObjectSortSentence
            , keyValueAttributeObjectSymbolSentence
            , keyOnlyAttributeObjectSymbolSentence
            ]
        , moduleAttributes = Attributes []
        }
