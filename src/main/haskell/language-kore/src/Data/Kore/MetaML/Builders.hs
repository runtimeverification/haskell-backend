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
import           Data.Kore.AST.MetaOrObject
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
    => s Meta SentenceMetaPattern Variable
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
    => s Meta SentenceMetaPattern Variable
    -> [MetaPatternStub]
    -> MetaPatternStub
applyS sentence = applyPS sentence []

isImplicitHead
    :: SentenceSymbolOrAlias s
    => s Meta SentenceMetaPattern Variable
    -> SymbolOrAlias Meta
    -> Bool
isImplicitHead sentence = (== getSentenceSymbolOrAliasHead sentence [])

-- |Creates a 'Meta' 'Sort' from a given 'MetaSortType'
sort_ :: MetaSortType -> Sort Meta
sort_ sortType =
    SortActualSort SortActual
        { sortActualName = Id (show sortType)
        , sortActualSorts = []
        }

-- |Given a string @name@, yields the 'UnsortedPatternStub' defining
-- name as a variable.
unparameterizedVariable_ :: String -> MetaPatternStub
unparameterizedVariable_ name =
    UnsortedPatternStub
        (\sortS ->
            VariablePattern Variable
                { variableName = Id name
                , variableSort = sortS
                }
        )

-- |Given a 'Sort' @sort@ and a string @name@, yields 'PatternStub' defining
-- name as a variable of sort @sort@.
parameterizedVariable_ :: Sort Meta -> String -> MetaPatternStub
parameterizedVariable_ sort = withSort sort . unparameterizedVariable_

-- |constructs an unparameterized Symbol declaration given the symbol name,
-- operand sorts and result sort.
symbol_ :: String -> [Sort Meta] -> Sort Meta -> MetaSentenceSymbol
symbol_ name = parameterizedSymbol_ name []

-- |constructs a Symbol declaration given symbol name, parameters,
-- operand sorts and result sort.
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

-- |A 'PatternStub' representing 'Bottom'.
bottom_ :: MetaPatternStub
bottom_ = UnsortedPatternStub (BottomPattern . Bottom)

-- |A 'PatternStub' representing 'Top'.
top_ :: MetaPatternStub
top_ = UnsortedPatternStub (BottomPattern . Bottom)

-- |Builds a 'PatternStub' representing 'Equals' given the sort of the
-- operands and their corresponding 'PatternStub's.
equalsS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equalsS_ s = equalsM_ (Just s)

-- |Builds a 'PatternStub' representing 'Equals' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
equals_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
equals_ = equalsM_ Nothing

-- |Builds a 'PatternStub' representing 'In' given the sort of the
-- operands and their corresponding 'PatternStub's.
inS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub -> MetaPatternStub
inS_ s = inM_ (Just s)

-- |Builds a 'PatternStub' representing 'In' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
in_ :: MetaPatternStub -> MetaPatternStub -> MetaPatternStub
in_ = inM_ Nothing

-- |Builds a PatternStub representing 'Ceil' given the sort of the
-- operand and its corresponding 'PatternStub's.
ceilS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub
ceilS_ s = ceilM_ (Just s)

-- |Builds a 'PatternStub' representing 'Ceil' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
ceil_ :: MetaPatternStub -> MetaPatternStub
ceil_ = ceilM_ Nothing

-- |Builds a 'PatternStub' representing 'Floor' given the sort of the
-- operand and its corresponding 'PatternStub's.
floorS_ :: Sort Meta -> MetaPatternStub -> MetaPatternStub
floorS_ s = floorM_ (Just s)

-- |Builds a 'PatternStub' representing 'Floor' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
floor_ :: MetaPatternStub -> MetaPatternStub
floor_ = floorM_ Nothing

-- |Builds a 'PatternStub' representing 'Exists' given a variable and an
-- operand 'PatternStub'.
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

-- |Builds a 'PatternStub' representing 'Forall' given a variable and an
-- operand 'PatternStub'.
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

-- |Builds a 'PatternStub' representing 'Or' given 'PatternStub's for its
-- operands.
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

-- |Builds a 'PatternStub' representing 'And' given 'PatternStub's for its
-- operands.
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

-- |Builds a 'PatternStub' representing 'Iff' given 'PatternStub's for its
-- operands.
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

-- |Builds a 'PatternStub' representing 'Implies' given 'PatternStub's for
-- its operands.
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

-- |Builds a 'PatternStub' representing 'Not' given a 'PatternStub' for
-- its operand.
not_ :: MetaPatternStub -> MetaPatternStub
not_ =
    unaryPattern
        (\sortS pattern1 ->
            NotPattern Not
                { notSort   = sortS
                , notChild  = pattern1
                }
        )
