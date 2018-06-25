{-|
Module      : Data.Kore.MetaML.Builders
Description : Safe way to build larger 'level' patterns from components.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.AST.Builders where

import           Data.Kore.AST.BuildersImpl
import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.ASTHelpers
import           Data.Kore.Error
import           Data.Fix

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: level -> String -> AstLocation -> SortVariable level
sortParameter _ name location =
    SortVariable Id
        { getId = name
        , idLocation = location
        }

{-|'applyPS' applies a symbol or alias declared by a given sentence to a list
of operands, using the provided sort arguments.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyPS
    :: SentenceSymbolOrAlias s
    => s level (Pattern level) Variable
    -> [Sort level]
    -> [CommonPurePatternStub level]
    -> CommonPurePatternStub level
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
    => s level (Pattern level) Variable
    -> [CommonPurePatternStub level]
    -> CommonPurePatternStub level
applyS sentence = applyPS sentence []

isImplicitHead
    :: SentenceSymbolOrAlias s
    => s level (Pattern level) Variable
    -> SymbolOrAlias level
    -> Bool
isImplicitHead sentence = (== getSentenceSymbolOrAliasHead sentence [])

-- |Creates a 'level' 'Sort' from a given 'MetaSortType'
sort_ :: MetaSortType -> Sort level
sort_ sortType =
    SortActualSort SortActual
        { sortActualName = Id
            { getId = show sortType
            , idLocation = AstLocationImplicit
            }
        , sortActualSorts = []
        }

-- |Given a string @name@, yields the 'UnsortedPatternStub' defining
-- name as a variable.
unparameterizedVariable_ :: String -> AstLocation -> CommonPurePatternStub level
unparameterizedVariable_ name location =
    UnsortedPatternStub
        (\sortS ->
            VariablePattern Variable
                { variableName = Id
                    { getId = name
                    , idLocation = location
                    }
                , variableSort = sortS
                }
        )

-- |Given a 'Sort' @sort@ and a string @name@, yields 'PatternStub' defining
-- name as a variable of sort @sort@.
parameterizedVariable_
    :: Sort level -> String -> AstLocation -> CommonPurePatternStub level
parameterizedVariable_ sort name location =
    withSort sort (unparameterizedVariable_ name location)

-- |constructs an unparameterized Symbol declaration given the symbol name,
-- operand sorts and result sort.
symbol_
    :: String
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
symbol_ name location = parameterizedSymbol_ name location []

-- |constructs a Symbol declaration given symbol name, parameters,
-- operand sorts and result sort.
parameterizedSymbol_
    :: String
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
parameterizedSymbol_ name location parameters operandSorts resultSort =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id
                { getId = name
                , idLocation = location
                }
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = operandSorts
        , sentenceSymbolResultSort = resultSort
        , sentenceSymbolAttributes = Attributes []
        }

-- |constructs an unparameterized Alias declaration given the alias name,
-- operand sorts and result sort.
alias_
    :: String
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> PureSentenceAlias level
alias_ name location = parameterizedAlias_ name location []

-- |constructs a Alias declaration given alias name, parameters,
-- operand sorts and result sort.
parameterizedAlias_
    :: String
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> PureSentenceAlias level
parameterizedAlias_ name location parameters operandSorts resultSort leftPat rightPat =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id
                { getId = name
                , idLocation = location
                }
            , aliasParams = parameters
            }
        , sentenceAliasSorts = operandSorts
        , sentenceAliasResultSort = resultSort
        , sentenceAliasLeftPattern = leftPat
        , sentenceAliasRightPattern = rightPat
        , sentenceAliasAttributes = Attributes []
        }

-- |A 'PatternStub' representing 'Bottom'.
bottom_ :: CommonPurePatternStub level
bottom_ = UnsortedPatternStub (BottomPattern . Bottom)

-- |A 'PatternStub' representing 'Top'.
top_ :: CommonPurePatternStub level
top_ = UnsortedPatternStub (TopPattern . Top)

-- |Builds a 'PatternStub' representing 'Equals' given the sort of the
-- operands and their corresponding 'PatternStub's.
equalsS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
equalsS_ s = equalsM_ (Just s)

-- |Builds a 'PatternStub' representing 'Equals' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
equals_
    :: (MetaOrObject level)
    => CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
equals_ = equalsM_ Nothing

-- |Builds a 'PatternStub' representing 'In' given the sort of the
-- operands and their corresponding 'PatternStub's.
inS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
inS_ s = inM_ (Just s)

-- |Builds a 'PatternStub' representing 'In' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
in_
    :: (MetaOrObject level)
    => CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
in_ = inM_ Nothing

-- |Builds a PatternStub representing 'Ceil' given the sort of the
-- operand and its corresponding 'PatternStub's.
ceilS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
ceilS_ s = ceilM_ (Just s)

-- |Builds a 'PatternStub' representing 'Ceil' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
ceil_
    :: (MetaOrObject level)
    => CommonPurePatternStub level -> CommonPurePatternStub level
ceil_ = ceilM_ Nothing

-- |Builds a 'PatternStub' representing 'Floor' given the sort of the
-- operand and its corresponding 'PatternStub's.
floorS_
    :: (MetaOrObject level)
    => Sort level -> CommonPurePatternStub level -> CommonPurePatternStub level
floorS_ s = floorM_ (Just s)

-- |Builds a 'PatternStub' representing 'Floor' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
floor_
    :: (MetaOrObject level)
    => CommonPurePatternStub level -> CommonPurePatternStub level
floor_ = floorM_ Nothing

-- |Builds a 'PatternStub' representing 'Exists' given a variable and an
-- operand 'PatternStub'.
exists_
    :: (MetaOrObject level)
    => Variable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
forall_
    :: Variable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
or_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
and_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
iff_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
implies_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
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
not_ :: CommonPurePatternStub level -> CommonPurePatternStub level
not_ =
    unaryPattern
        (\sortS pattern1 ->
            NotPattern Not
                { notSort   = sortS
                , notChild  = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'Next' given a 'PatternStub' for
-- its operand.
next_ :: CommonPurePatternStub Object -> CommonPurePatternStub Object
next_ =
    unaryPattern
        (\sortS pattern1 ->
            NextPattern Next
                { nextSort   = sortS
                , nextChild  = pattern1
                }
        )
