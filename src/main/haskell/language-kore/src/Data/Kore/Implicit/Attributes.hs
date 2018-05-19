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
    , uncheckedAttributesModule
    ) where

import           Data.Kore.AST.Common
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
              :: KoreSentenceSort Object
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
    asSentence
        ( SentenceSymbol
            { sentenceSymbolSymbol     = Symbol
                { symbolConstructor = Id hookName AstLocationImplicit
                , symbolParams      = []
                }
            , sentenceSymbolSorts      = [hookObjectSort AstLocationImplicit]
            , sentenceSymbolResultSort = attributeObjectSort AstLocationImplicit
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object
        )

{-| `hookAttribute` creates a hook attribute pattern containing the given
string.
-}
hookAttribute :: String -> AstLocation -> CommonKorePattern
hookAttribute hook location =
    asObjectKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id hookName AstLocationImplicit
                , symbolOrAliasParams      = []
                }
            , applicationChildren      =
                [ asKorePattern
                    ( DomainValuePattern DomainValue
                        { domainValueSort  = hookObjectSort location
                        , domainValueChild =
                            asKorePattern
                                (StringLiteralPattern (StringLiteral hook))
                        }
                    )
                ]
            }
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
            , argumentPositionObjectSortSentence
            , firstArgumentObjectSymbolSentence
            , secondArgumentObjectSymbolSentence
            , thirdArgumentObjectSymbolSentence
            , fourthArgumentObjectSymbolSentence
            , fifthArgumentObjectSymbolSentence
            , strictObjectSortSentence
            , strictObjectSymbolSentence
            , associativeObjectSymbolSentence
            , commutativeObjectSymbolSentence
            ]
        , moduleAttributes = Attributes []
        }
