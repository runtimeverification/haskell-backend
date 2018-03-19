module Data.Kore.MetaML.Builders ( module Data.Kore.MetaML.Builders
                                 , MetaPatternStub
                                 ) where

import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.ASTHelpers
import           Data.Kore.Error
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.BuildersImpl

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: String -> SortVariable Meta
sortParameter name = SortVariable (Id name)

{-|'fillCheckSorts' matches a list of sorts to a list of 'MetaPatternStub',
checking that the sorts are identical where possible, creating a pattern with
the provided sort otherwise.
-}
fillCheckSorts :: [Sort Meta] -> [MetaPatternStub] -> [CommonMetaPattern]
fillCheckSorts [] []         = []
fillCheckSorts [] _          = error "Not enough sorts!"
fillCheckSorts _ []          = error "Not enough patterns!"
fillCheckSorts (s:ss) (p:ps) = fillCheckSort s p : fillCheckSorts ss ps

{-|'fillCheckSorts' matches a sort to a 'MetaPatternStub', checking
that the pattern's sorts is identical if possible, creating a pattern with the
provided sort otherwise.
-}
fillCheckSort :: Sort Meta -> MetaPatternStub -> CommonMetaPattern
fillCheckSort
    desiredSort
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = actualSort }
    )
  =
    if desiredSort /= actualSort
    then error
        (  "Unmatched sorts, expected:\n"
        ++ show desiredSort
        ++ "\nbut got:\n"
        ++ show actualSort
        ++ "\nfor pattern\n"
        ++ show p
        ++ "."
        )
    else Fix p
fillCheckSort desiredSort (UnsortedPatternStub p) =
    Fix (p desiredSort)

{-|'applyPS' applies a symbol or alias declared by a given sentence to a list
of operands, using the provided sort arguments.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyPS
    :: SentenceSymbolOrAlias s
    => s MetaAttributes Meta
    -> [Sort Meta]
    -> [MetaPatternStub]
    -> MetaPatternStub
applyPS sentence sortParameters patterns =
    SortedPatternStub SortedPattern
        { sortedPatternPattern =
            ApplicationPattern Application
                { applicationSymbolOrAlias = SymbolOrAlias
                    { symbolOrAliasConstructor =
                        getSentenceSymbolOrAliasConstructor sentence
                    , symbolOrAliasParams = sortParameters
                    }
                , applicationChildren = fillCheckSorts argumentSorts patterns
                }
        , sortedPatternSort = returnSort
        }
  where
    applicationSorts =
        case symbolOrAliasSorts sortParameters sentence of
            Left err -> error (printError err)
            Right as -> as
    returnSort = applicationSortsResult applicationSorts
    argumentSorts = applicationSortsOperands applicationSorts

{-|'applyS' applies a symbol or alias without sort arguments, declared by a
given sentence, to a list of operands.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyS
    :: SentenceSymbolOrAlias s
    => s MetaAttributes Meta -> [MetaPatternStub] -> MetaPatternStub
applyS sentence = applyPS sentence []

sort_ :: MetaSortType -> Sort Meta
sort_ sortType =
    SortActualSort SortActual
        { sortActualName = Id (show sortType)
        , sortActualSorts = []
        }

unparameterizedVariable_ :: String -> MetaPatternStub
unparameterizedVariable_ name =
    UnsortedPatternStub
        (\sortS ->
            VariablePattern Variable
                { variableName = Id name
                , variableSort = sortS
                }
        )

parameterizedVariable_ :: Sort Meta -> String -> MetaPatternStub
parameterizedVariable_ sort = withSort sort . unparameterizedVariable_

symbol_ :: String -> [Sort Meta] -> Sort Meta -> MetaSentenceSymbol
symbol_ name = parameterizedSymbol_ name []

parameterizedSymbol_
    :: String -> [SortVariable Meta] -> [Sort Meta] -> Sort Meta
    -> MetaSentenceSymbol
parameterizedSymbol_ name parameters operandSorts resultSort =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = operandSorts
        , sentenceSymbolResultSort = resultSort
        , sentenceSymbolAttributes = MetaAttributes []
        }

equalsS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equalsS_ s =
    binarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            firstPattern
            secondPattern
          ->
            EqualsPattern Equals
                { equalsOperandSort = childSort
                , equalsResultSort  = resultSort
                , equalsFirst       = firstPattern
                , equalsSecond      = secondPattern
                }
        )
        (Just (ChildSort s))

equals_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equals_ =
    binarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            firstPattern
            secondPattern
          ->
            EqualsPattern Equals
                { equalsOperandSort = childSort
                , equalsResultSort  = resultSort
                , equalsFirst       = firstPattern
                , equalsSecond      = secondPattern
                }
        )
        Nothing

exists_ :: Variable Meta -> MetaPatternStub -> MetaPatternStub
exists_ variable1 =
    unaryPattern
        (\sortS pattern1 ->
            ExistsPattern Exists
                { existsSort     = sortS
                , existsVariable = variable1
                , existsChild    = pattern1
                }
        )

or_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
or_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            OrPattern Or
                { orSort   = commonSort
                , orFirst  = firstPattern
                , orSecond = secondPattern
                }
        )

and_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
and_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            AndPattern And
                { andSort   = commonSort
                , andFirst  = firstPattern
                , andSecond = secondPattern
                }
        )

implies_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
implies_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            ImpliesPattern Implies
                { impliesSort   = commonSort
                , impliesFirst  = firstPattern
                , impliesSecond = secondPattern
                }
        )

not_ :: MetaPatternStub -> MetaPatternStub
not_ =
    unaryPattern
        (\sortS pattern1 ->
            NotPattern Not
                { notSort   = sortS
                , notChild  = pattern1
                }
        )
