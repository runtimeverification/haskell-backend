{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Kore.Implicit.ImplicitKore
Description : Builds the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.ImplicitKore
    ( uncheckedKoreModule
    , str_
    , char_
    , sortList_
    , patternList_
    , sortA
    , mlPatternA
    , mlPatternP
    , variable
    ) where

import           Data.Functor.Classes
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Kore.AST.Builders
import Kore.AST.Pure
import Kore.AST.Sentence
import Kore.Implicit.ImplicitSorts
import Kore.Implicit.ImplicitVarsInternal
import Kore.MetaML.AST

{-
Conventions used:

Variables start with 'v', a variable called '#a' will be denoted by the 'va'
Haskell name. A variable may end with an apostrophe.

Meta sorts are denoted by their name in camelCase followed by @MetaSort@,
e.g. patternListMetaSort.

Constructors of meta objects that correspond to lexical symbols are followed by
an underscore, e.g. symbol_, equals_.

Some of the helper functions for building meta-objects are denoted in the same
way, e.g. sort_.

-}

implicitSymbol
    :: Text
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level domain
implicitSymbol name = symbol_ name AstLocationImplicit

implicitParameterizedSymbol
    :: Text
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level domain
implicitParameterizedSymbol name = parameterizedSymbol_ name AstLocationImplicit

epsilon = implicitSymbol "#epsilon" [] stringMetaSort

sort = implicitSymbol "#sort" [stringMetaSort, sortListMetaSort] sortMetaSort

sortA
    ::  ( Functor domain
        , Show1 domain
        , Show (Pattern Meta domain Variable child)
        , child ~ CommonPurePattern Meta domain
        )
    => [CommonPurePatternStub Meta domain]
    -> CommonPurePatternStub Meta domain
sortA = applyS sort

symbol =
    implicitSymbol
        "#symbol"
        [stringMetaSort, sortListMetaSort, sortListMetaSort, sortMetaSort]
        symbolMetaSort

getArgumentSorts =
    implicitSymbol "#getArgumentSorts" [symbolMetaSort] sortListMetaSort

getReturnSort = implicitSymbol "#getReturnSort" [symbolMetaSort] sortMetaSort

variable =
    implicitSymbol "#variable" [stringMetaSort, sortMetaSort] variableMetaSort

applicationP =
    implicitSymbol
        "#application" [symbolMetaSort, patternListMetaSort] patternMetaSort

mlPatternA :: MLPatternType -> ([MetaPatternStub] -> MetaPatternStub)
mlPatternA patternType = applyS (mlPatternP patternType)

mlPatternP :: MLPatternType -> MetaSentenceSymbol
mlPatternP AndPatternType =
    implicitSymbol
        "#\\and"
        [sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP BottomPatternType =
    implicitSymbol "#\\bottom" [sortMetaSort] patternMetaSort
mlPatternP CeilPatternType =
    implicitSymbol
        "#\\ceil"
        [sortMetaSort, sortMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP DomainValuePatternType =
    implicitSymbol
        "#\\dv"
        [sortMetaSort, stringMetaSort]
        patternMetaSort
mlPatternP EqualsPatternType =
    implicitSymbol
        "#\\equals"
        [sortMetaSort, sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP ExistsPatternType =
    implicitSymbol
        "#\\exists"
        [sortMetaSort, variableMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP FloorPatternType =
    implicitSymbol
        "#\\floor"
        [sortMetaSort, sortMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP ForallPatternType =
    implicitSymbol
        "#\\forall"
        [sortMetaSort, variableMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP IffPatternType =
    implicitSymbol
        "#\\iff"
        [sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP ImpliesPatternType =
    implicitSymbol
        "#\\implies"
        [sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP InPatternType =
    implicitSymbol
        "#\\in"
        [sortMetaSort, sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP NextPatternType =
    implicitSymbol "#\\next" [sortMetaSort, patternMetaSort] patternMetaSort
mlPatternP NotPatternType =
    implicitSymbol "#\\not" [sortMetaSort, patternMetaSort] patternMetaSort
mlPatternP OrPatternType =
    implicitSymbol
        "#\\or"
        [sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP RewritesPatternType =
    implicitSymbol
        "#\\rewrites"
        [sortMetaSort, patternMetaSort, patternMetaSort]
        patternMetaSort
mlPatternP TopPatternType =
    implicitSymbol "#\\top" [sortMetaSort] patternMetaSort


[ andP, bottomP, ceilP, dvP, equalsP, existsP, floorP, forallP, iffP, impliesP,
  inP, nextP, notP, orP, rewritesP, topP] = map mlPatternP allPatternTypes

variableAsPattern =
    implicitSymbol "#variableAsPattern" [variableMetaSort] patternMetaSort

variablePattern =
    implicitSymbol
        "#variablePattern" [stringMetaSort, sortMetaSort] patternMetaSort

getFV = implicitSymbol "#getFV" [patternMetaSort] variableListMetaSort
getFVFromPatterns = implicitSymbol "#getFVFromPatterns" [patternListMetaSort] variableListMetaSort

occursFree =
    implicitParameterizedSymbol
        "#occursFree" [pS] [variableMetaSort, patternMetaSort] spS

freshName = implicitSymbol "#freshName" [patternListMetaSort] stringMetaSort

substitute =
    implicitSymbol
        "#substitute"
        [patternMetaSort, patternMetaSort, variableMetaSort]
        patternMetaSort
substitutePatterns =
    implicitSymbol "#substitutePatterns"
        [patternListMetaSort, patternMetaSort, variableMetaSort]
        patternListMetaSort

-- 7.6 Matching Logic Theories

sortDeclared =
    implicitParameterizedSymbol "#sortDeclared" [pS] [sortMetaSort] spS
symbolDeclared =
    implicitParameterizedSymbol "#symbolDeclared" [pS] [symbolMetaSort] spS
axiomDeclared =
    implicitParameterizedSymbol "#axiomDeclared" [pS] [patternMetaSort] spS

sortsDeclared =
    implicitParameterizedSymbol "#sortsDeclared" [pS] [sortListMetaSort] spS

wellFormedPatterns =
    implicitParameterizedSymbol
        "#wellFormedPatterns" [pS] [patternListMetaSort] spS

getSort = implicitSymbol "#getSort" [patternMetaSort] sortMetaSort

getSortsFromPatterns =
    implicitSymbol
        "#getSortsFromPatterns" [patternListMetaSort] sortListMetaSort

{-|'wellFormedImpliesProvableAxiom' is a special case for an axioms of the form
#wellFormed(phi) -> #provable(phi), which covers most axioms encoded in the
meta-theory of K.
-}

wellFormed =
    implicitParameterizedSymbol "#wellFormed" [pS] [patternMetaSort] spS

char_ :: Char -> MetaPatternStub
char_ c =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = CharLiteralPattern (CharLiteral c)
        , sortedPatternSort    = charMetaSort
        }

str_ :: Text -> MetaPatternStub
str_ s =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = StringLiteralPattern (StringLiteral s)
        , sortedPatternSort    = stringMetaSort
        }

sortList_ :: [MetaPatternStub] -> MetaPatternStub
sortList_ = foldr (\p ps -> consSortListA [p, ps]) nilSortListA

patternList_ :: [MetaPatternStub] -> MetaPatternStub
patternList_ = foldr (\p ps -> consPatternListA [p, ps]) nilPatternListA

-- 7.7 Matching logic Proof System

provable = implicitParameterizedSymbol "#provable" [pS] [patternMetaSort] spS

ceilBT = implicitSymbol "#`ceil" [sortMetaSort, sortMetaSort] symbolMetaSort


metaSortDescription
    :: MetaSortType -> Sentence Meta sortParam patternType
metaSortDescription sortType =
    SentenceSortSentence SentenceSort
        { sentenceSortName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
  where
    sentenceSortName = Id
        { getId = Text.pack (show sortType)
        , idLocation = AstLocationImplicit
        }

uncheckedKoreModule :: MetaModule
uncheckedKoreModule =
    Module
        { moduleName       = ModuleName "kore"
        , moduleSentences  =
            (metaSortDescription <$> metaSortsList)

            ++
            [ asSentence nilCharList, asSentence consCharList
            , asSentence appendCharList
            , asSentence inCharList
            , asSentence deleteCharList

            , asSentence nilSortList, asSentence consSortList
            , asSentence appendSortList
            , asSentence inSortList
            , asSentence deleteSortList

            , asSentence nilSymbolList, asSentence consSymbolList
            , asSentence appendSymbolList
            , asSentence inSymbolList
            , asSentence deleteSymbolList

            , asSentence nilVariableList, asSentence consVariableList
            , asSentence appendVariableList
            , asSentence inVariableList
            , asSentence deleteVariableList

            , asSentence nilPatternList, asSentence consPatternList
            , asSentence appendPatternList
            , asSentence inPatternList
            , asSentence deletePatternList

            , asSentence epsilon

            , asSentence sort

            , asSentence symbol

            , asSentence getArgumentSorts

            , asSentence getReturnSort

            , asSentence variable

            , asSentence applicationP
            , asSentence andP
            , asSentence notP
            , asSentence existsP

            , asSentence variableAsPattern

            , asSentence variablePattern

            , asSentence orP
            , asSentence impliesP
            , asSentence iffP
            , asSentence forallP
            , asSentence ceilP
            , asSentence floorP
            , asSentence equalsP
            , asSentence inP
            , asSentence topP
            , asSentence bottomP
            , asSentence dvP
            , asSentence nextP
            , asSentence rewritesP

            , asSentence getFV
            , asSentence getFVFromPatterns

            , asSentence occursFree

            , asSentence freshName

            , asSentence substitute
            , asSentence substitutePatterns

            , asSentence sortDeclared
            , asSentence symbolDeclared
            , asSentence axiomDeclared

            , asSentence sortsDeclared

            , asSentence wellFormed

            , asSentence wellFormedPatterns

            , asSentence getSort

            , asSentence getSortsFromPatterns

            , asSentence provable

            , asSentence ceilBT
            ]
        , moduleAttributes = Attributes []
        }
