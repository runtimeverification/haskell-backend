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
    , smtlibAttribute
    , functionalAttribute
    , functionAttribute
    , constructorAttribute
    , uncheckedAttributesModule
    , ImplicitAttributes
    ) where

import           Data.Default
import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTUtils.SmartConstructors


data ImplicitAttributes =
    ImplicitAttributes
    {
    }

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

keyOnlyAttribute :: String -> CommonKorePattern
keyOnlyAttribute key = asObjectKorePattern
    ( ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor =
                Id keyOnlyAttributeLabel AstLocationImplicit
            , symbolOrAliasParams      = []
            }
        , applicationChildren =
            [ asObjectKorePattern
                ( DomainValuePattern DomainValue
                    { domainValueSort =
                        attributeKeyObjectSort AstLocationImplicit
                    , domainValueChild = Fix
                        (StringLiteralPattern (StringLiteral key))
                    }
                )
            ]
        }
    )

implicitGroundHead :: String -> SymbolOrAlias level
implicitGroundHead = groundHead AstLocationImplicit

keyValueAttribute :: String -> String -> CommonKorePattern
keyValueAttribute key value = asObjectKorePattern
    ( ApplicationPattern Application
        { applicationSymbolOrAlias =
                implicitGroundHead keyValueAttributeLabel
        , applicationChildren =
            [ asObjectKorePattern
                ( DomainValuePattern DomainValue
                    { domainValueSort =
                        attributeKeyObjectSort AstLocationImplicit
                    , domainValueChild = Fix
                        (StringLiteralPattern (StringLiteral key))
                    }
                )
            , asObjectKorePattern
                ( DomainValuePattern DomainValue
                    { domainValueSort =
                        attributeValueObjectSort AstLocationImplicit
                    , domainValueChild = Fix
                        (StringLiteralPattern (StringLiteral value))
                    }
                )
            ]
        }
    )

data KeyValueAttribute =
    KeyValueAttribute
    { key   :: String
    , value :: Maybe String
    }

attributeToKeyValueAttribute :: CommonKorePattern -> Maybe KeyValueAttribute
attributeToKeyValueAttribute p =
    case patternKoreToPure p of
        Right (App_ h children) ->
            if h == implicitGroundHead keyValueAttributeLabel then
                case children of
                    [DV _ k, DV _ v] -> Just KeyValueAttribute
                        { key = k
                        , value = Just v
                        }
                    _ -> Nothing
            else if h == implicitGroundHead keyOnlyAttributeLabel then
                case children of
                    [DV _ k] -> Just KeyValueAttribute
                        { key = k
                        , value = Nothing
                        }
            else Nothing
        _ -> Nothing


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

functionAttribute :: CommonKorePattern
functionAttribute  = simpleAttribute "function"

functionalAttribute :: CommonKorePattern
functionalAttribute  = simpleAttribute "functional"

constructorAttribute :: CommonKorePattern
constructorAttribute = simpleAttribute "constructor"

{-| Creates a Pattern for an attribute
consisting of a single keyword with no arguments.
-}
simpleAttribute :: String -> CommonKorePattern
simpleAttribute name = asObjectKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id name AstLocationImplicit
                , symbolOrAliasParams      = []
                }
            , applicationChildren = []
            }
        )

{-| Creates a sentence declaring a simpleAttribute
-}
simpleAttributeSentence :: String -> KoreSentence
simpleAttributeSentence name =
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol     = Symbol
                { symbolConstructor = Id name AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = []
            , sentenceSymbolResultSort = attributeObjectSort AstLocationImplicit
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object
        )

noArgumentOrParameterSentence :: String -> Sort Object -> KoreSentence
noArgumentOrParameterSentence name sort =
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol     = Symbol
                { symbolConstructor = Id name AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = []
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object
        )

associativeObjectSymbolSentence :: KoreSentence
associativeObjectSymbolSentence =
    noArgumentOrParameterSentence
        "associative"
        (attributeObjectSort AstLocationImplicit)

commutativeObjectSymbolSentence :: KoreSentence
commutativeObjectSymbolSentence =
    noArgumentOrParameterSentence
        "commutative"
        (attributeObjectSort AstLocationImplicit)

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
