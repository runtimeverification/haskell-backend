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
    ( attributeSort
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
import           Data.Kore.Implicit.ImplicitSorts (stringMetaSort)


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


noParameterSortAndSentence
    :: String -> (AstLocation -> Sort Meta, KoreSentence)
noParameterSortAndSentence name =
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
        :: KoreSentenceSort Meta
        )
    )

{-| 'attributeSort' is the sort for all top-level attribute patterns
-}
attributeSort :: AstLocation -> Sort Meta
attributeSortSentence :: KoreSentence
(attributeSort, attributeSortSentence) =
    noParameterSortAndSentence "#Attribute"

keyValueAttributeLabel :: String
keyValueAttributeLabel = "#keyVal"

keyOnlyAttributeLabel :: String
keyOnlyAttributeLabel = "#key"

keyValueAttributeSymbolSentence :: KoreSentence
keyValueAttributeSymbolSentence =
    attributeSymbolSentence keyValueAttributeLabel
        [stringMetaSort, stringMetaSort]

keyOnlyAttributeSymbolSentence :: KoreSentence
keyOnlyAttributeSymbolSentence =
    attributeSymbolSentence keyOnlyAttributeLabel [stringMetaSort]

implicitGroundHead :: String -> SymbolOrAlias level
implicitGroundHead = (`groundHead` AstLocationImplicit)

attributeToKeyValueAttribute :: CommonKorePattern -> Maybe KeyValueAttribute
attributeToKeyValueAttribute p =
    case patternKoreToPure Meta p of
        Right (App_ h children)
          | h == implicitGroundHead keyValueAttributeLabel ->
                case children of
                    [ ~ (StringLiteral_ (StringLiteral k)),
                        ~ (StringLiteral_ (StringLiteral v))]
                        -> Just KeyValueAttribute
                            { key = k
                            , value = Just v
                            }
                    _ -> Nothing
          |  h == implicitGroundHead keyOnlyAttributeLabel ->
                case children of
                    [~ (StringLiteral_ (StringLiteral k))] ->
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
        [(StringLiteral_ (StringLiteral k))]
    )

keyValueAttribute :: String -> String -> CommonKorePattern
keyValueAttribute k v = patternPureToKore
    (App_ (implicitGroundHead keyValueAttributeLabel)
        [ (StringLiteral_ (StringLiteral k))
        , (StringLiteral_ (StringLiteral v))
        ]
    )

attributeSymbolSentence
  :: String                       -- ^ attribute symbol
  -> [Sort Meta]                  -- ^ argument sorts
  -> KoreSentence
attributeSymbolSentence name sorts =
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol  = Symbol
                { symbolConstructor = Id name AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = sorts
            , sentenceSymbolResultSort = attributeSort AstLocationImplicit
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Meta
        )

{-| 'uncheckedAttributesModule' contains declarations for all symbols visible
in attributes;
-}
uncheckedAttributesModule :: KoreModule
uncheckedAttributesModule =
    Module
        { moduleName       = ModuleName "BUILTIN-attributes"
        , moduleSentences  =
            [ attributeSortSentence
            , keyValueAttributeSymbolSentence
            , keyOnlyAttributeSymbolSentence
            ]
        , moduleAttributes = Attributes []
        }
