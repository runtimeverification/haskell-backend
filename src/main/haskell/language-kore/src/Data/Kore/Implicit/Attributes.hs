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
    , supportedKoreAttributesModule
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.Sentence

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

keyValueAttributeObjectSymbolSentence :: KoreSentence
keyValueAttributeObjectSymbolSentence =
    attributeObjectSymbolSentence "keyValueAttribute"
        [attributeKeyObjectSort, attributeValueObjectSort]

keyOnlyAttributeObjectSymbolSentence :: KoreSentence
keyOnlyAttributeObjectSymbolSentence =
    attributeObjectSymbolSentence "keyOnlyAttribute" [attributeKeyObjectSort]

-- | `sort SmtLib{} []`
smtlibObjectSort :: AstLocation -> Sort Object
smtlibObjectSortSentence :: KoreSentence
(smtlibObjectSort, smtlibObjectSortSentence) =
    noParameterObjectSortAndSentence "SmtLib"

smtlibObjectSymbolSentence :: KoreSentence
smtlibObjectSymbolSentence =
    attributeObjectSymbolSentence "smtlib" [smtlibObjectSort]


-- | example: `smtlib{}(\dv{SmtLib{}}("and"))`
smtlibAttribute :: String -> AstLocation -> CommonKorePattern
smtlibAttribute smtlibSymbol location =
    singleDomainValueAttribute "smtlib" smtlibSymbol $ smtlibObjectSort location

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

{- | `singleDomainValueAttribute` creates an attribute pattern with a single domain value argument
for example:
        hook{}(\\dv{Hook{}}(".Set"))
        smtlib{}(\\dv{SmtLib{}}("and"))
-}
singleDomainValueAttribute
  :: String      -- ^ Attribute name
  -> String      -- ^ Domain value
  -> Sort Object -- ^ Attribute sort
  -> CommonKorePattern
singleDomainValueAttribute name domainValue sort =
    asObjectKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id name AstLocationImplicit
                , symbolOrAliasParams      = []
                }
            , applicationChildren      =
                [ asKorePattern
                    ( DomainValuePattern DomainValue
                        { domainValueSort  = sort
                        , domainValueChild =
                            asKorePattern
                                (StringLiteralPattern (StringLiteral domainValue))
                        }
                    )
                ]
            }
        )

functionAttribute :: CommonKorePattern
functionAttribute  = simpleAttribute "function"

functionSymbolSentence :: KoreSentence
functionSymbolSentence  = simpleAttributeSentence "function"

functionalAttribute :: CommonKorePattern
functionalAttribute  = simpleAttribute "functional"

functionalSymbolSentence :: KoreSentence
functionalSymbolSentence  = simpleAttributeSentence "functional"

constructorAttribute :: CommonKorePattern
constructorAttribute = simpleAttribute "constructor"

constructorSymbolSentence :: KoreSentence
constructorSymbolSentence  = simpleAttributeSentence "constructor"

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

supportedKoreAttributesModule :: KoreModule
supportedKoreAttributesModule =
    Module
        { moduleName       = ModuleName "BUILTIN-attributes"
        , moduleSentences  =
            [ attributeObjectSortSentence
            , attributeKeyObjectSortSentence
            , attributeValueObjectSortSentence
            , keyValueAttributeObjectSymbolSentence
            , keyOnlyAttributeObjectSymbolSentence
            , smtlibObjectSortSentence
            , smtlibObjectSymbolSentence
            , functionalSymbolSentence
            , functionSymbolSentence
            , constructorSymbolSentence
            , associativeObjectSymbolSentence
            , commutativeObjectSymbolSentence
            ]
        , moduleAttributes = Attributes []
        }
