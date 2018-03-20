{-|
Module      : Data.Kore.MetaML.Builders
Description : Safe way to build larger 'Meta' patterns from components.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.MetaML.Builders ( module Data.Kore.MetaML.Builders
                                 , MetaPatternStub
                                 ) where

import           Data.Kore.AST.Common
import           Data.Kore.ASTHelpers
import           Data.Kore.Error
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.BuildersImpl

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: String -> SortVariable Meta
sortParameter name = SortVariable (Id name)

{-|'applyPS' applies a symbol or alias declared by a given sentence to a list
of operands, using the provided sort arguments.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyPS
    :: SentenceSymbolOrAlias s
    => s CommonMetaPattern Meta
    -> [Sort Meta]
    -> [MetaPatternStub]
    -> MetaPatternStub
applyPS sentence sortParameters patterns =
    SortedPatternStub SortedPattern
        { sortedPatternPattern =
            ApplicationPattern Application
                { applicationSymbolOrAlias =
                    getSentenceSymbolOrAliasHead sentence sortParameters
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
    => s CommonMetaPattern Meta -> [MetaPatternStub] -> MetaPatternStub
applyS sentence = applyPS sentence []

isImplicitHead
    :: SentenceSymbolOrAlias s
    => s CommonMetaPattern Meta
    -> SymbolOrAlias Meta
    -> Bool
isImplicitHead sentence = (== getSentenceSymbolOrAliasHead sentence [])

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
        , sentenceSymbolAttributes = Attributes []
        }

bottom_ :: MetaPatternStub
bottom_ = UnsortedPatternStub (BottomPattern . Bottom)

top_ :: MetaPatternStub
top_ = UnsortedPatternStub (BottomPattern . Bottom)

equalsM_
    :: Maybe (Sort Meta)
    -> (MetaPatternStub -> MetaPatternStub -> MetaPatternStub)
equalsM_ s =
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
        (ChildSort <$> s)

equalsS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equalsS_ s = equalsM_ (Just s)

equals_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equals_ = equalsM_ Nothing

inM_
    :: Maybe (Sort Meta)
    -> (MetaPatternStub -> MetaPatternStub -> MetaPatternStub)
inM_ s =
    binarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            firstPattern
            secondPattern
          ->
            InPattern In
                { inOperandSort     = childSort
                , inResultSort      = resultSort
                , inContainedChild  = firstPattern
                , inContainingChild = secondPattern
                }
        )
        (ChildSort <$> s)

inS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub -> MetaPatternStub
inS_ s = inM_ (Just s)

in_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
in_ = inM_ Nothing

ceilM_ :: Maybe (Sort Meta) -> MetaPatternStub -> MetaPatternStub
ceilM_ s =
    unarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            childPattern
          ->
            CeilPattern Ceil
                { ceilOperandSort = childSort
                , ceilResultSort  = resultSort
                , ceilChild       = childPattern
                }
        )
        (ChildSort <$> s)

ceilS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub
ceilS_ s = ceilM_ (Just s)

ceil_ :: MetaPatternStub -> MetaPatternStub
ceil_ = ceilM_ Nothing

floorM_ :: Maybe (Sort Meta) -> MetaPatternStub -> MetaPatternStub
floorM_ s =
    unarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            childPattern
          ->
            FloorPattern Floor
                { floorOperandSort = childSort
                , floorResultSort  = resultSort
                , floorChild       = childPattern
                }
        )
        (ChildSort <$> s)

floorS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub
floorS_ s = floorM_ (Just s)

floor_ :: MetaPatternStub -> MetaPatternStub
floor_ = floorM_ Nothing

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

forall_ :: Variable Meta -> MetaPatternStub -> MetaPatternStub
forall_ variable1 =
    unaryPattern
        (\sortS pattern1 ->
            ForallPattern Forall
                { forallSort     = sortS
                , forallVariable = variable1
                , forallChild    = pattern1
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

iff_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
iff_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            IffPattern Iff
                { iffSort   = commonSort
                , iffFirst  = firstPattern
                , iffSecond = secondPattern
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
