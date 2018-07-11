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
    , hookAttribute
    , smtlibAttribute
    , functionalAttribute
    , constructorAttribute
    , uncheckedAttributesModule
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject

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

hookObjectSort :: AstLocation -> Sort Object
hookObjectSortSentence :: KoreSentence
(hookObjectSort, hookObjectSortSentence) =
    noParameterObjectSortAndSentence "Hook"


hookName :: String
hookName = "hook"

hookObjectSymbolSentence :: KoreSentence
hookObjectSymbolSentence =
  attributeObjectSymbolSentence hookName hookObjectSort

{-| `hookAttribute` creates a hook attribute pattern containing the given
string.
-}
hookAttribute :: String -> AstLocation -> CommonKorePattern
hookAttribute hook location =
    singleDomainValueAttribute hookName hook $ hookObjectSort location

-- | `sort SmtLib{} []`
smtlibObjectSort :: AstLocation -> Sort Object
smtlibObjectSortSentence :: KoreSentence
(smtlibObjectSort, smtlibObjectSortSentence) =
    noParameterObjectSortAndSentence "SmtLib"

smtlibObjectSymbolSentence :: KoreSentence
smtlibObjectSymbolSentence =
  attributeObjectSymbolSentence "smtlib" smtlibObjectSort


-- | example: `smtlib{}(\dv{SmtLib{}}("and"))`
smtlibAttribute :: String -> AstLocation -> CommonKorePattern
smtlibAttribute smtlibSymbol location =
    singleDomainValueAttribute "smtlib" smtlibSymbol $ smtlibObjectSort location

attributeObjectSymbolSentence
  :: String                       -- ^ attribute symbol
  -> (AstLocation -> Sort Object) -- ^ argument sort constructor
  -> KoreSentence
attributeObjectSymbolSentence name sort = 
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol  = Symbol
                { symbolConstructor = Id name AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = [sort AstLocationImplicit]
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


argumentPositionObjectSort :: AstLocation -> Sort Object
argumentPositionObjectSortSentence :: KoreSentence
(argumentPositionObjectSort, argumentPositionObjectSortSentence) =
    noParameterObjectSortAndSentence "ArgumentPosition"

firstArgumentObjectSymbolSentence :: KoreSentence
firstArgumentObjectSymbolSentence =
    noArgumentOrParameterSentence
        "firstArgument"
        (argumentPositionObjectSort AstLocationImplicit)

secondArgumentObjectSymbolSentence :: KoreSentence
secondArgumentObjectSymbolSentence =
    noArgumentOrParameterSentence
        "secondArgument"
        (argumentPositionObjectSort AstLocationImplicit)

thirdArgumentObjectSymbolSentence :: KoreSentence
thirdArgumentObjectSymbolSentence =
    noArgumentOrParameterSentence
        "thirdArgument"
        (argumentPositionObjectSort AstLocationImplicit)

fourthArgumentObjectSymbolSentence :: KoreSentence
fourthArgumentObjectSymbolSentence =
    noArgumentOrParameterSentence
        "fourthArgument"
        (argumentPositionObjectSort AstLocationImplicit)

fifthArgumentObjectSymbolSentence :: KoreSentence
fifthArgumentObjectSymbolSentence =
    noArgumentOrParameterSentence
        "fifthArgument"
        (argumentPositionObjectSort AstLocationImplicit)

strictObjectSort :: AstLocation -> Sort Object
strictObjectSortSentence :: KoreSentence
(strictObjectSort, strictObjectSortSentence) =
    noParameterObjectSortAndSentence "Strict"

strictObjectSymbolSentence :: KoreSentence
strictObjectSymbolSentence =
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol     = Symbol
                { symbolConstructor = Id "strict" AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      =
                [ strictObjectSort AstLocationImplicit
                , argumentPositionObjectSort AstLocationImplicit
                ]
            , sentenceSymbolResultSort = attributeObjectSort AstLocationImplicit
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object
        )

seqstrictObjectSymbolSentence :: KoreSentence
seqstrictObjectSymbolSentence =
  attributeObjectSymbolSentence "seqstrict" strictObjectSort

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
            , hookObjectSortSentence
            , hookObjectSymbolSentence
            , smtlibObjectSortSentence
            , smtlibObjectSymbolSentence
            , functionalSymbolSentence
            , constructorSymbolSentence
            , argumentPositionObjectSortSentence
            , firstArgumentObjectSymbolSentence
            , secondArgumentObjectSymbolSentence
            , thirdArgumentObjectSymbolSentence
            , fourthArgumentObjectSymbolSentence
            , fifthArgumentObjectSymbolSentence
            , strictObjectSortSentence
            , strictObjectSymbolSentence
            , seqstrictObjectSymbolSentence
            , associativeObjectSymbolSentence
            , commutativeObjectSymbolSentence
            ]
        , moduleAttributes = Attributes []
        }
