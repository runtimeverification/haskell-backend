{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Kore.Implicit.ImplicitKore
Description : Builds the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
    , applicationA
    , mlPatternA
    , mlPatternP
    , symbolA
    , variableA
    , variable
    , sortsDeclaredA
    , sortDeclaredA
    , symbolDeclaredA
    ) where

import Kore.AST.Builders
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureSentenceSymbol )
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

parameterizedEqualsAxiom
    :: [SortVariable Meta]
    -> MetaPatternStub
    -> MetaPatternStub
    -> MetaSentenceAxiom
parameterizedEqualsAxiom parameters =
    parameterizedEqualsAxiom_ parameters
        (sortParameter Meta "#esp" AstLocationImplicit)

equalsAxiom
    :: MetaPatternStub
    -> MetaPatternStub
    -> MetaSentenceAxiom
equalsAxiom = parameterizedEqualsAxiom []

implicitSymbol
    :: String
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
implicitSymbol name = symbol_ name AstLocationImplicit

implicitParameterizedSymbol
    :: String
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
implicitParameterizedSymbol name = parameterizedSymbol_ name AstLocationImplicit

epsilon = implicitSymbol "#epsilon" [] stringMetaSort
epsilonA = applyS epsilon []
epsilonAxiom = equalsAxiom epsilonA nilCharListA

sort = implicitSymbol "#sort" [stringMetaSort, sortListMetaSort] sortMetaSort
sortA = applyS sort

symbol =
    implicitSymbol
        "#symbol"
        [stringMetaSort, sortListMetaSort, sortListMetaSort, sortMetaSort]
        symbolMetaSort
symbolA = applyS symbol

getArgumentSorts =
    implicitSymbol "#getArgumentSorts" [symbolMetaSort] sortListMetaSort
getArgumentSortsA = applyS getArgumentSorts
getArgumentSortsAxiom =
    equalsAxiom (getArgumentSortsA [symbolA [vf, vS, vS', vs]]) vS'

getReturnSort = implicitSymbol "#getReturnSort" [symbolMetaSort] sortMetaSort
getReturnSortA = applyS getReturnSort
getReturnSortAxiom =
    equalsAxiom (getReturnSortA [symbolA [vf, vS, vS', vs]]) vs

variable =
    implicitSymbol "#variable" [stringMetaSort, sortMetaSort] variableMetaSort
variableA = applyS variable

applicationP =
    implicitSymbol
        "#application" [symbolMetaSort, patternListMetaSort] patternMetaSort
applicationA = applyS applicationP

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

[ andA, bottomA, ceilA, _ {-dvA-}, equalsA, existsA, floorA, forallA, iffA,
  impliesA, inA, _ {-nextA-}, notA, orA, _ {-rewritesA-}, topA] =
    map mlPatternA allPatternTypes

[ andP, bottomP, ceilP, dvP, equalsP, existsP, floorP, forallP, iffP, impliesP,
  inP, nextP, notP, orP, rewritesP, topP] = map mlPatternP allPatternTypes

variableAsPattern =
    implicitSymbol "#variableAsPattern" [variableMetaSort] patternMetaSort
variableAsPatternA = applyS variableAsPattern
variableAsPatternAxiom =
    parameterizedAxiom_
        [pS]
        (withSort spS
            (implies_
                (not_ (equalsS_ variableMetaSort v1 v2))
                (not_
                    (equals_
                        (variableAsPatternA [v1])
                        (variableAsPatternA [v2])
                    )
                )
            )
        )

variablePattern =
    implicitSymbol
        "#variablePattern" [stringMetaSort, sortMetaSort] patternMetaSort
variablePatternA = applyS variablePattern
variablePatternAxiom =
    equalsAxiom
        (variablePatternA [vx, vs])
        (variableAsPatternA [variableA [vx, vs]])

patternAxioms =
    [ equalsAxiom
        (orA [vs, vphi, vpsi])
        (notA [vs, andA [vs, notA [vs, vphi], notA[vs, vpsi]]])
    , equalsAxiom
        (impliesA [vs, vphi, vpsi])
        (orA [vs, notA [vs, vphi], vpsi])
    , equalsAxiom
        (iffA [vs, vphi, vpsi])
        (andA [vs, impliesA [vs, vphi, vpsi], impliesA [vs, vphi, vpsi]])
    , equalsAxiom
        (forallA [vs, v, vphi])
        (notA [vs, existsA [vs, v, notA [vs, vphi]]])
    , equalsAxiom
        (ceilA [vs1, vs2, vphi])
        (applicationA
            [ceilBTA [vs1, vs2], consPatternListA [vphi, nilPatternListA]]
        )
    , equalsAxiom
        (floorA [vs1, vs2, vphi])
        (notA [vs2, ceilA [vs1, vs2, notA [vs1, vphi]]])
    , equalsAxiom
        (equalsA [vs1, vs2, vphi, vpsi])
        (floorA [vs1, vs2, iffA [vs1, vphi, vpsi]])
    , equalsAxiom
        (inA [vs1, vs2, vphi, vpsi])
        (ceilA [vs1, vs2, andA [vs1, vphi, vpsi]])
    , equalsAxiom
        (topA [vs])
        (existsA
            [ vs
            , variableA [vx, vs]
            , variableAsPatternA [variableA [vx, vs]]
            ]
        )
    , equalsAxiom
        (bottomA [vs])
        (notA [vs, topA [vs]])
    ]

getFV = implicitSymbol "#getFV" [patternMetaSort] variableListMetaSort
getFVA = applyS getFV
getFVFromPatterns = implicitSymbol "#getFVFromPatterns" [patternListMetaSort] variableListMetaSort
getFVFromPatternsA = applyS getFVFromPatterns

getFVAxioms =
    [ equalsAxiom
        (getFVA [variableAsPatternA [v]])
        (consVariableListA [v, nilVariableListA])
    , equalsAxiom
        (getFVA [applicationA [vsigma, vL]])
        (getFVFromPatternsA [vL])
    , equalsAxiom
        (getFVA [andA [vs, vphi, vpsi]])
        (appendVariableListA [getFVA [vphi], getFVA [vpsi]])
    , equalsAxiom
        (getFVA [notA [vs, vphi]])
        (getFVA [vphi])
    , equalsAxiom
        (getFVA [existsA [vs, v, vphi]])
        (deleteVariableListA [v, getFVA [vphi]])
    , equalsAxiom
        (getFVFromPatternsA [nilPatternListA])
        nilVariableListA
    , equalsAxiom
        (getFVFromPatternsA [consPatternListA [vphi, vL]])
        (appendVariableListA [getFVA [vphi], getFVFromPatternsA [vL]])
    ]

occursFree =
    implicitParameterizedSymbol
        "#occursFree" [pS] [variableMetaSort, patternMetaSort] spS
occursFreeA = applyPS occursFree
occursFreeAxiom =
    parameterizedEqualsAxiom [pS]
        (occursFreeA [spS] [v, vphi])
        (inVariableListA [spS] [v, getFVA [vphi]])

freshName = implicitSymbol "#freshName" [patternListMetaSort] stringMetaSort
freshNameA = applyS freshName
freshNameAxiom =
    parameterizedAxiom_ [pS]
        (not_
            (inVariableListA [spS]
                [variableA [freshNameA [vL], vs], getFVFromPatternsA [vL]]
            )
        )

substitute =
    implicitSymbol
        "#substitute"
        [patternMetaSort, patternMetaSort, variableMetaSort]
        patternMetaSort
substituteA = applyS substitute
substitutePatterns =
    implicitSymbol "#substitutePatterns"
        [patternListMetaSort, patternMetaSort, variableMetaSort]
        patternListMetaSort
substitutePatternsA = applyS substitutePatterns

substitutePatternAxioms =
    [ equalsAxiom
        (substituteA [variableAsPatternA [vu], vpsi, v])
        (or_
            (and_ (equalsS_ variableMetaSort vu v) vpsi)
            (and_
                (not_ (equalsS_ variableMetaSort vu v))
                (variableAsPatternA [vu])
            )
        )
    , equalsAxiom
        (substituteA [applicationA [vsigma, vL], vpsi, v])
        (applicationA [vsigma, substitutePatternsA [vL, vpsi, v]])
    , equalsAxiom
        (substituteA [orA [vs, vphi1, vphi2], vpsi, v])
        (orA [vs, substituteA [vphi1, vpsi, v], substituteA [vphi2, vpsi, v]])
    , equalsAxiom
        (substituteA [notA [vs, vphi], vpsi, v])
        (notA [vs, substituteA [vphi, vpsi, v]])
    , equalsAxiom
        (substituteA [existsA [vs', variableA [vx, vs], vphi], vpsi, v])
        (exists_ (stringVariable_ "#x'")
            (and_
                (equals_
                    vx'
                    (freshNameA
                        [patternList_ [vphi, vpsi, variableAsPatternA [v]]]
                    )
                )
                (existsA
                    [ vs'
                    , variableA [vx', vs]
                    , substituteA
                        [ substituteA
                            [ vphi
                            , variableAsPatternA [variableA [vx', vs]]
                            , variableA [vx, vs]
                            ]
                        , vpsi
                        , v
                        ]
                    ]
                )
            )
        )
    , equalsAxiom
        (substitutePatternsA [nilPatternListA, vpsi, v])
        nilPatternListA
    , equalsAxiom
        (substitutePatternsA [consPatternListA [vphi, vL], vpsi, v])
        (consPatternListA
            [substituteA [vphi, vpsi, v], substitutePatternsA [vL, vpsi, v]]
        )
    ]

alphaEquivalenceAxiom =
    parameterizedAxiom_ [pS]
        (implies_
            (and_
                (not_ (occursFreeA [spS] [v1, vphi]))
                (not_ (occursFreeA [spS] [v2, vphi]))
            )
            (equals_
                (existsA
                    [vs, v1, substituteA [vphi, variableAsPatternA [v1], vu]])
                (existsA
                    [vs, v2, substituteA [vphi, variableAsPatternA [v2], vu]])
            )
        )

-- 7.6 Matching Logic Theories

sortDeclared =
    implicitParameterizedSymbol "#sortDeclared" [pS] [sortMetaSort] spS
sortDeclaredA = applyPS sortDeclared
symbolDeclared =
    implicitParameterizedSymbol "#symbolDeclared" [pS] [symbolMetaSort] spS
symbolDeclaredA = applyPS symbolDeclared
axiomDeclared =
    implicitParameterizedSymbol "#axiomDeclared" [pS] [patternMetaSort] spS
axiomDeclaredA = applyPS axiomDeclared

sortsDeclared =
    implicitParameterizedSymbol "#sortsDeclared" [pS] [sortListMetaSort] spS
sortsDeclaredA = applyPS sortsDeclared
sortsDeclaredAxioms =
    [ parameterizedAxiom_ [pS] (sortsDeclaredA [spS] [nilSortListA])
    , parameterizedEqualsAxiom [pS]
        (sortsDeclaredA [spS] [consSortListA [vs, vS]])
        (and_ (sortDeclaredA [spS] [vs]) (sortsDeclaredA [spS] [vS]))
    ]

ceilBTDeclaredAxiom =
    parameterizedAxiom_ [pS]
        (implies_
            (and_ (sortDeclaredA [spS] [vs1]) (sortDeclaredA [spS] [vs2]))
            (symbolDeclaredA [spS] [ceilBTA [vs1, vs2]])
        )

wellFormedPatterns =
    implicitParameterizedSymbol
        "#wellFormedPatterns" [pS] [patternListMetaSort] spS
wellFormedPatternsA = applyPS wellFormedPatterns
wellFormedPatternsAxioms =
    [ parameterizedAxiom_ [pS]
        (wellFormedPatternsA [spS] [nilPatternListA])
    , parameterizedEqualsAxiom [pS]
        (wellFormedPatternsA [spS] [consPatternListA [vphi, vL]])
        (and_ (wellFormedA [spS] [vphi]) (wellFormedPatternsA [spS] [vL]))
    ]

getSort = implicitSymbol "#getSort" [patternMetaSort] sortMetaSort
getSortA = applyS getSort

getSortsFromPatterns =
    implicitSymbol
        "#getSortsFromPatterns" [patternListMetaSort] sortListMetaSort
getSortsFromPatternsA = applyS getSortsFromPatterns
getSortsFromPattersAxioms =
    [ equalsAxiom
        (getSortsFromPatternsA [nilPatternListA])
        nilSortListA
    , equalsAxiom
        (getSortsFromPatternsA [consPatternListA [vphi, vL]])
        (consSortListA [getSortA [vphi], getSortsFromPatternsA [vL]])
    ]

wellFormedGetSortAxioms =
    [ parameterizedEqualsAxiom [pS]
        (wellFormedA [spS] [variableAsPatternA [variableA [vx, vs]]])
        (sortDeclaredA [spS] [vs])
    , parameterizedEqualsAxiom [pS]
        (wellFormedA [spS] [applicationA [vsigma, vL]])
        (and_
            (and_
                (symbolDeclaredA [spS] [vsigma])
                (wellFormedPatternsA [spS] [vL])
            )
            (and_
                (sortDeclaredA [spS] [getReturnSortA [vsigma]])
                (equals_
                    (getSortsFromPatternsA [vL])
                    (getArgumentSortsA [vsigma])
                )
            )
        )
    , parameterizedEqualsAxiom [pS]
        (wellFormedA [spS] [andA [vs, vphi, vpsi]])
        (and_
            (and_
                (wellFormedA [spS] [vphi])
                (wellFormedA [spS] [vpsi])
            )
            (and_
                (equals_ (getSortA [vphi]) vs)
                (equals_ (getSortA [vpsi]) vs)
            )
        )
    , parameterizedEqualsAxiom [pS]
        (wellFormedA [spS] [notA [vs, vphi]])
        (and_
            (wellFormedA [spS] [vphi])
            (equals_ (getSortA [vpsi]) vs)
        )
    , parameterizedEqualsAxiom [pS]
        (wellFormedA [spS] [existsA [vs, v, vphi]])
        (and_
            (wellFormedA [spS] [variableAsPatternA [v]])
            (and_
                (wellFormedA [spS] [vphi])
                (equals_ (getSortA [vpsi]) vs)
            )
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [variableAsPatternA [variableA [vx, vs]]])
        (and_
            (wellFormedA
                [sortMetaSort]
                [variableAsPatternA [variableA [vx, vs]]]
            )
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [applicationA [vsigma, vL]])
        (and_
            (wellFormedA [sortMetaSort] [applicationA [vsigma, vL]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [andA [vs, vphi, vpsi]])
        (and_
            (wellFormedA [sortMetaSort] [andA [vs, vphi, vpsi]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [notA [vs, vphi]])
        (and_
            (wellFormedA [sortMetaSort] [notA [vs, vphi]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [existsA [vs, v, vphi]])
        (and_
            (wellFormedA [sortMetaSort] [existsA [vs, v, vphi]])
            vs
        )
    ]

{-|'wellFormedImpliesProvableAxiom' is a special case for an axioms of the form
#wellFormed(phi) -> #provable(phi), which covers most axioms encoded in the
meta-theory of K.
-}
wellFormedImpliesProvableAxiom :: MetaPatternStub -> MetaSentenceAxiom
wellFormedImpliesProvableAxiom pattern1 =
    parameterizedAxiom_ [pS]
        (implies_
            (wellFormedA [spS] [pattern1])
            (provableA [spS] [pattern1])
        )

wellFormed =
    implicitParameterizedSymbol "#wellFormed" [pS] [patternMetaSort] spS
wellFormedA = applyPS wellFormed

char_ :: Char -> MetaPatternStub
char_ c =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = CharLiteralPattern (CharLiteral c)
        , sortedPatternSort    = charMetaSort
        }

str_ :: String -> MetaPatternStub
str_ s =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = StringLiteralPattern (StringLiteral s)
        , sortedPatternSort    = stringMetaSort
        }

sortList_ :: [MetaPatternStub] -> MetaPatternStub
sortList_ = foldr (\p ps -> consSortListA [p, ps]) nilSortListA

patternList_ :: [MetaPatternStub] -> MetaPatternStub
patternList_ = foldr (\p ps -> consPatternListA [p, ps]) nilPatternListA

stringVariable_ :: String -> Variable Meta
stringVariable_ name =
    Variable
        { variableName = Id
            { getId = name
            , idLocation = AstLocationImplicit
            }
        , variableSort = stringMetaSort
        }

-- 7.7 Matching logic Proof System

provable = implicitParameterizedSymbol "#provable" [pS] [patternMetaSort] spS
provableA = applyPS provable

propositionalLogicAxioms =
    [ wellFormedImpliesProvableAxiom
        (impliesA [vs, vphi, impliesA [vs, vpsi, vphi]])
    , wellFormedImpliesProvableAxiom
        (impliesA
            [ vs
            , impliesA [vs, vphi1, impliesA [vs, vphi2, vphi3]]
            , impliesA
                [ vs
                , impliesA [vs, vphi1, vphi2]
                , impliesA [vs, vphi1, vphi3]]
            ]
        )
    , wellFormedImpliesProvableAxiom
        (impliesA
            [ vs
            , impliesA [vs, notA [vs, vpsi], notA [vs, vphi]]
            , impliesA [vs, vphi, vpsi]
            ]
        )
    -- modus ponens
    , parameterizedAxiom_ [pS]
        (implies_
            (and_
                (wellFormedA [spS] [vphi])
                (and_
                    (wellFormedA [spS] [vpsi])
                    (wellFormedA [spS] [impliesA [vs, vphi, vpsi]])
                )
            )
            (implies_
                (and_
                    (provableA [spS] [vphi])
                    (provableA [spS] [impliesA [vs, vphi, vpsi]])
                )
                (provableA [spS] [vpsi])
            )
        )
    ]

firstOrderLogicWithEqualityAxioms =
    -- forall
    [ let
        forallFormula =
            forallA
                [ vs
                , v
                , impliesA
                    [ vs
                    , impliesA [vs, vphi, vpsi]
                    , impliesA [vs, vphi, forallA [vs, v, vpsi]]
                    ]
                ]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [variableAsPatternA [v]])
                    (and_
                        (wellFormedA [spS] [vphi])
                        (wellFormedA [spS] [forallFormula])
                    )
                )
                (implies_
                    (not_ (occursFreeA [spS] [v, vphi]))
                    (provableA [spS] [forallFormula])
                )
            )
    -- universal generalization
    , parameterizedAxiom_ [pS]
        (implies_
            (and_
                (wellFormedA [spS] [vphi])
                (wellFormedA [spS] [forallA [vs, v, vphi]])
            )
            (implies_
                (provableA [spS] [vphi])
                (provableA [spS] [forallA [vs, v, vphi]])
            )
        )
    -- functional substitution
    , let
        substitutionFormula =
            impliesA
                [ vs2
                , andA
                    [ vs2
                    , existsA
                        [ vs2
                        , vu
                        , equalsA [vs1, vs2, variableAsPatternA [vu], vpsi]
                        ]
                    , forallA [vs2, v, vphi]
                    ]
                , substituteA [vphi, vpsi, v]
                ]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [vpsi])
                    (wellFormedA [spS] [substitutionFormula])
                )
                (implies_
                    (occursFreeA [spS] [vu, vphi])
                    (provableA [spS] [substitutionFormula])
                )
            )
    -- functional variable
    , wellFormedImpliesProvableAxiom
        (existsA [vs2, vu, equalsA [vs1, vs2, variableAsPatternA [vu], v]])
    -- equality introduction
    , wellFormedImpliesProvableAxiom
        (equalsA [vs1, vs2, vphi, vphi])
    -- equality elimination
    , wellFormedImpliesProvableAxiom
        (impliesA
            [vs2
            , equalsA [vs1, vs2, vphi1, vphi2]
            , impliesA
                [ vs2
                , substituteA [vpsi, vphi1, v]
                , substituteA [vpsi, vphi2, v]
                ]
            ]
        )
    ]

definednessAxiom =
    wellFormedImpliesProvableAxiom
        (ceilA [vs, vs', variableAsPatternA [variableA [vx, vs]]])

membershipAxioms =
    -- membership introduction
    [ let
        introductionFormula = inA [vs1, vs2, variableAsPatternA [v], vphi]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [vphi])
                    (and_
                        (wellFormedA [spS] [variableAsPatternA [v]])
                        (wellFormedA [spS] [introductionFormula])
                    )
                )
                (implies_
                    (and_
                        (provableA [spS] [vphi])
                        (not_ (occursFreeA [spS] [v, vphi]))
                    )
                    (provableA [spS] [introductionFormula])
                )
            )
    -- membership elimination
    , let
        introductionFormula = inA [vs1, vs2, variableAsPatternA [v], vphi]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [vphi])
                    (and_
                        (wellFormedA [spS] [variableAsPatternA [v]])
                        (wellFormedA [spS] [introductionFormula])
                    )
                )
                (implies_
                    (and_
                        (provableA [spS] [introductionFormula])
                        (not_ (occursFreeA [spS] [v, vphi]))
                    )
                    (provableA [spS] [vphi])
                )
            )
    -- membership variable
    , wellFormedImpliesProvableAxiom
        (equalsA [vs2, vs3, inA [vs1, vs2, v, vu], equalsA [vs1, vs2, v, vu]])
    -- membership and
    , wellFormedImpliesProvableAxiom
        (equalsA
            [ vs2
            , vs3
            , inA [vs1, vs2, v, andA [vs1, vphi, vpsi]]
            , andA [vs2, inA [vs1, vs2, v, vphi], inA [vs1, vs2, v, vpsi]]
            ]
        )
    -- membership not
    , wellFormedImpliesProvableAxiom
        (equalsA
            [ vs2
            , vs3
            , inA [vs1, vs2, v, notA [vs1, vphi]]
            , notA [vs2, inA [vs1, vs2, v, vphi]]
            ]
        )
    -- membership forall
    , let
        forallFormula =
            equalsA
                [ vs2
                , vs3
                , inA
                    [vs1, vs2, variableAsPatternA [v], forallA [vs1, vu, vphi]]
                , forallA
                    [vs2, vu, inA [vs1, vs2, variableAsPatternA [v], vphi]]]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [variableAsPatternA [vu]])
                    (and_
                        (wellFormedA [spS] [variableAsPatternA [v]])
                        (wellFormedA [spS] [forallFormula])
                    )
                )
                (implies_
                    (not_ (equalsS_ variableMetaSort vu v))
                    (provableA [spS] [forallFormula])
                )
            )
    -- membership symbol
    , let
        sigmaFormula pattern1 =
            applicationA
                [ vsigma
                , appendPatternListA [vL, consPatternListA [pattern1, vR]]]
        membershipFormula =
            equalsA
                [ vs2
                , vs3
                , inA [vs1, vs2, variableAsPatternA [v], sigmaFormula vphii]
                , existsA
                    [ vs2
                    , vu
                    , andA
                        [ vs2
                        , inA [vs1, vs2, variableAsPatternA [vu], vphii]
                        , inA
                            [ vs1
                            , vs2
                            , variableAsPatternA [v]
                            , sigmaFormula (variableAsPatternA [vu])
                            ]
                        ]
                    ]
                ]
      in
        parameterizedAxiom_ [pS]
            (implies_
                (and_
                    (and_
                        (wellFormedA [spS] [variableAsPatternA [vu]])
                        (wellFormedA [spS] [variableAsPatternA [v]])
                    )
                    (and_
                        (wellFormedA [spS] [sigmaFormula vphii])
                        (wellFormedA [spS] [membershipFormula])
                    )
                )
                (implies_
                    (and_
                        (not_ (equalsS_ variableMetaSort vu v))
                        (not_ (occursFreeA [spS] [vu, sigmaFormula vphii]))
                    )
                    (provableA [spS] [membershipFormula])
                )
            )
    ]

axiomAxiom =
    parameterizedAxiom_ [pS]
        (implies_
            (wellFormedA [spS] [vphi])
            (implies_
                (axiomDeclaredA [spS] [vphi])
                (provableA [spS] [vphi])
            )
        )

ceilBT = implicitSymbol "#`ceil" [sortMetaSort, sortMetaSort] symbolMetaSort
ceilBTA = applyS ceilBT
ceilBTAxiom =
    equalsAxiom
        (ceilBTA [vs, vs'])
        (symbolA [str_ "ceil", sortList_ [vs, vs'], sortList_ [vs], vs'])

uncheckedKoreModule :: MetaModule
uncheckedKoreModule =
    Module
        { moduleName       = ModuleName "kore"
        , moduleSentences  =
            [ asSentence nilCharList, asSentence consCharList
            , asSentence appendCharList
            , asSentence inCharList
            , asSentence deleteCharList
            ]
            ++ map asSentence charListAxioms

            ++
            [ asSentence nilSortList, asSentence consSortList
            , asSentence appendSortList
            , asSentence inSortList
            , asSentence deleteSortList
            ]
            ++ map asSentence sortListAxioms

            ++
            [ asSentence nilSymbolList, asSentence consSymbolList
            , asSentence appendSymbolList
            , asSentence inSymbolList
            , asSentence deleteSymbolList
            ]
            ++ map asSentence symbolListAxioms

            ++
            [ asSentence nilVariableList, asSentence consVariableList
            , asSentence appendVariableList
            , asSentence inVariableList
            , asSentence deleteVariableList
            ]
            ++ map asSentence variableListAxioms

            ++
            [ asSentence nilPatternList, asSentence consPatternList
            , asSentence appendPatternList
            , asSentence inPatternList
            , asSentence deletePatternList
            ]
            ++ map asSentence patternListAxioms

            ++
            [ asSentence epsilon
            , asSentence epsilonAxiom

            , asSentence sort

            , asSentence symbol

            , asSentence getArgumentSorts
            , asSentence getArgumentSortsAxiom

            , asSentence getReturnSort
            , asSentence getReturnSortAxiom

            , asSentence variable

            , asSentence applicationP
            , asSentence andP
            , asSentence notP
            , asSentence existsP

            , asSentence variableAsPattern
            , asSentence variableAsPatternAxiom

            , asSentence variablePattern
            , asSentence variablePatternAxiom

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
            ]
            ++ map asSentence patternAxioms

            ++
            [ asSentence getFV
            , asSentence getFVFromPatterns
            ]

            ++ map asSentence getFVAxioms

            ++
            [ asSentence occursFree
            , asSentence occursFreeAxiom

            , asSentence freshName
            , asSentence freshNameAxiom

            , asSentence substitute
            , asSentence substitutePatterns
            ]

            ++ map asSentence substitutePatternAxioms

            ++
            [ asSentence alphaEquivalenceAxiom

            , asSentence sortDeclared
            , asSentence symbolDeclared
            , asSentence axiomDeclared

            , asSentence sortsDeclared
            ]

            ++ map asSentence sortsDeclaredAxioms

            ++
            [ asSentence ceilBTDeclaredAxiom

            , asSentence wellFormed

            , asSentence wellFormedPatterns
            ]
            ++ map asSentence wellFormedPatternsAxioms

            ++
            [ asSentence getSort

            , asSentence getSortsFromPatterns
            ]
            ++ map asSentence getSortsFromPattersAxioms
            ++ map asSentence wellFormedGetSortAxioms

            ++ [ asSentence provable ]
            ++ map asSentence propositionalLogicAxioms
            ++ map asSentence firstOrderLogicWithEqualityAxioms
            ++ [ asSentence definednessAxiom ]
            ++ map asSentence membershipAxioms
            ++ [ asSentence axiomAxiom ]

            ++
            [ asSentence ceilBT
            , asSentence ceilBTAxiom
            ]
        , moduleAttributes = Attributes []
        }
