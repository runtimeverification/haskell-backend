{-|
Module      : Data.Kore.Implicit.ImplicitKore
Description : Builds the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.ImplicitKore
    (implicitKoreModule, implicitKoreDefinition) where

import           Data.Kore.AST
import           Data.Kore.ASTHelpers
import           Data.Kore.ASTVerifier.DefinitionVerifier (verifyDefinition)
import           Data.Kore.ASTVerifier.Error              (VerifyError)
import           Data.Kore.Error                          (Error, printError)
import           Data.Kore.Variables.Free                 (freeVariables)

import           Data.Foldable                            (foldl')
import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set

{-
Conventions used:

Variables start with 'v', a variable called '#a' will be denoted by the 'va'
Haskell name. A variable may end with an apostrophe.

Meta sorts are denoted by their name in camelCase followed by an
apostrophe, e.g. patternList'.

Constructors of meta objects that correspond to lexical symbols are followed by
an underscore, e.g. symbol_, equals_.

Some of the helper functions for building meta-objects are denoted in the same
way, e.g. sort_.

-}

type PatternMetaType = Pattern Meta Variable (FixedPattern Variable)

{-|'PatternM' is either a meta pattern with a known sort, or a function that
builds a meta pattern from a sort.
-}
data PatternM
  = SortedPatternM
        { patternMPattern :: !PatternMetaType
        , patternMSort    :: !(Sort Meta)
        }
  | UnsortedPatternM (Sort Meta -> PatternMetaType)

{-|'dummySort' is used in error messages when we want to convert an
'UnsortedPatternM' to a pattern that can be displayed.
-}
dummySort :: Sort Meta
dummySort = SortVariableSort (SortVariable (Id "#dummy"))

{-|'applyPS' applies a symbol or alias declared by a given sentence to a list
of operands, using the provided sort arguments.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyPS
    :: SentenceSymbolOrAlias s
    => s Meta
    -> [Sort Meta]
    -> [PatternM]
    -> PatternM
applyPS sentence sortParameters patterns =
    SortedPatternM
        { patternMPattern =
            ApplicationPattern Application
                { applicationSymbolOrAlias = SymbolOrAlias
                    { symbolOrAliasConstructor =
                        getSentenceSymbolOrAliasConstructor sentence
                    , symbolOrAliasParams = sortParameters
                    }
                , applicationChildren = fillCheckSorts argumentSorts patterns
                }
        , patternMSort = returnSort
        }
  where
    applicationSorts =
        case symbolOrAliasSorts sortParameters sentence of
            Left err -> error (printError err)
            Right as -> as
    returnSort = applicationSortsResult applicationSorts
    argumentSorts = applicationSortsOperands applicationSorts

{-|'applyP' applies a symbol or alias without sort arguments, declared by a
given sentence, to a list of operands.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyS :: SentenceSymbolOrAlias s => s Meta -> [PatternM] -> PatternM
applyS sentence = applyPS sentence []

{-|'fillCheckSorts' matches a list of sorts to a list of 'PatternM', checking
that the sorts are identical where possible, creating a pattern with the
provided sort otherwise.
-}
fillCheckSorts :: [Sort Meta] -> [PatternM] -> [UnifiedPattern]
fillCheckSorts [] []         = []
fillCheckSorts [] _          = error "Not enough sorts!"
fillCheckSorts _ []          = error "Not enough patterns!"
fillCheckSorts (s:ss) (p:ps) = fillCheckSort s p : fillCheckSorts ss ps

{-|'fillCheckSorts' matches a sort to a 'PatternM', checking
that the pattern's sorts is identical if possible, creating a pattern with the
provided sort otherwise.
-}
fillCheckSort :: Sort Meta -> PatternM -> UnifiedPattern
fillCheckSort
    desiredSort
    SortedPatternM { patternMPattern = p, patternMSort = actualSort }
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
    else asUnifiedPattern p
fillCheckSort desiredSort (UnsortedPatternM p) =
    asUnifiedPattern (p desiredSort)

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: String -> SortVariable Meta
sortParameter name = SortVariable (Id name)

{-|'equalsSortParam' is the sort param implicitly used for 'equals' when no
other sort can be inferred.
-}
equalsSortParam :: SortVariable Meta
equalsSortParam = sortParameter "#esp"

equalsSort :: Sort Meta
equalsSort = SortVariableSort equalsSortParam

{-|'withSort' transforms an 'UnsortedPatternM' in a 'SortedPatternM'.
-}
withSort :: Sort Meta -> PatternM -> PatternM
withSort s (UnsortedPatternM p) =
    SortedPatternM
        { patternMPattern = p s
        , patternMSort = s
        }
withSort
    s
    p@SortedPatternM { patternMSort = existingSort }
  =
    if s == existingSort
        then p
        else
            error
                (  "Unmatched sorts: "
                ++ show s
                ++ " and "
                ++ show existingSort
                ++ "."
                )

{-|'parameterizedAxiom' creates an axiom that has sort parameters from
a pattern.
-}
parameterizedAxiom :: [SortVariable Meta] -> PatternM -> SentenceAxiom
parameterizedAxiom _ (UnsortedPatternM p) =
    error ("Cannot infer sort for " ++ show (p dummySort) ++ ".")
parameterizedAxiom
    parameters
    SortedPatternM { patternMPattern = p, patternMSort = s }
  =
    SentenceAxiom
        { sentenceAxiomParameters = map asUnified parameters
        , sentenceAxiomPattern = quantifyFreeVariables s (MetaPattern p)
        , sentenceAxiomAttributes = Attributes []
        }

{-|'parameterizedEqualsAxiom' is a special case for a 'parameterizedAxiom' that
contains an equals pattern.
-}
parameterizedEqualsAxiom
    :: [SortVariable Meta] -> PatternM -> PatternM -> SentenceAxiom
parameterizedEqualsAxiom parameters first second =
    parameterizedAxiom
        (equalsSortParam : parameters)
        (withSort equalsSort (equals_ first second))

{-|'equalsAxiom' is a special case for an axiom that contains an equals pattern.
-}
equalsAxiom :: PatternM -> PatternM -> SentenceAxiom
equalsAxiom = parameterizedEqualsAxiom []

{-|'wellFormedImpliesProvableAxiom' is a special case for an axioms of the form
#wellFormed(phi) -> #provable(phi), which covers most axioms encoded in the
meta-theory of K.
-}
wellFormedImpliesProvableAxiom :: PatternM -> SentenceAxiom
wellFormedImpliesProvableAxiom pattern1 =
    parameterizedAxiom [pS]
        (implies_
            (wellFormedA [spS] [pattern1])
            (provableA [spS] [pattern1])
        )

{-|'fillCheckPairSorts' takes two 'PatternM' objects, assumes that they must
have the same sort, and tries to build 'UnifiedPattern's from them if possible,
otherwise it returns functions that can build 'UnifiedPattern's.
-}
fillCheckPairSorts
    :: PatternM
    -> PatternM
    -> Either
        (Sort Meta -> UnifiedPattern, Sort Meta -> UnifiedPattern)
        (Sort Meta, UnifiedPattern, UnifiedPattern)
fillCheckPairSorts (UnsortedPatternM first) (UnsortedPatternM second) =
    Left (asUnifiedPattern . first, asUnifiedPattern . second)
fillCheckPairSorts
    (UnsortedPatternM first)
    SortedPatternM { patternMPattern = second, patternMSort = s }
  =
    Right
        ( s
        , asUnifiedPattern (first s)
        , asUnifiedPattern second
        )
fillCheckPairSorts
    SortedPatternM { patternMPattern = first, patternMSort = s }
    (UnsortedPatternM second)
  =
    Right
        ( s
        , asUnifiedPattern first
        , asUnifiedPattern (second s)
        )
fillCheckPairSorts
    SortedPatternM { patternMPattern = p1, patternMSort = actualSort1 }
    SortedPatternM { patternMPattern = p2, patternMSort = actualSort2 }
  =
    if actualSort1 /= actualSort2
        then error
            (  "Unmatched sorts: "
            ++ show actualSort1
            ++ " and "
            ++ show actualSort2
            ++ "."
            )
        else
            Right
                ( actualSort1
                , asUnifiedPattern p1
                , asUnifiedPattern p2
                )

{-|'quantifyFreeVariables' quantifies all free variables in the given pattern.
It assumes that the pattern has the provided sort.
-}
-- TODO(virgil): Make this generic and move it in ASTHelpers.hs
quantifyFreeVariables :: Sort Meta -> UnifiedPattern -> UnifiedPattern
quantifyFreeVariables s p =
    foldl'
        (wrapAndQuantify s)
        p
        (checkUnique (Set.map asMeta (freeVariables p)))
  where
    asMeta (MetaVariable var) = var

wrapAndQuantify
    :: Sort Meta -> UnifiedPattern -> Variable Meta -> UnifiedPattern
wrapAndQuantify s p var =
    MetaPattern
        (ForallPattern Forall
            { forallSort = s
            , forallVariable = var
            , forallChild = p
            }
        )

checkUnique
    :: Set.Set (Variable Meta) -> Set.Set (Variable Meta)
checkUnique variables =
    case checkUniqueEither (Set.toList variables) Map.empty of
        Right _  -> variables
        Left err -> error err

checkUniqueEither
    :: [Variable Meta]
    -> Map.Map String (Variable Meta)
    -> Either String ()
checkUniqueEither [] _ = Right ()
checkUniqueEither (var:vars) indexed =
    case Map.lookup name indexed of
        Nothing -> checkUniqueEither vars (Map.insert name var indexed)
        Just existingV ->
            Left
                (  "Conflicting variables: "
                ++ show var
                ++ " and "
                ++ show existingV
                ++ "."
                )
  where
    name = getId (variableName var)

{-|'unaryPattern' is a helper for building 'PatternM's for unary operators
like \not.
-}
unaryPattern
    :: (Sort Meta -> UnifiedPattern -> PatternMetaType)
    -> PatternM
    -> PatternM
unaryPattern
    constructor
    SortedPatternM { patternMPattern = p, patternMSort = s }
  =
    SortedPatternM
        { patternMPattern = constructor s (asUnifiedPattern p)
        , patternMSort    = s
        }
unaryPattern constructor (UnsortedPatternM p) =
    UnsortedPatternM (\sortS -> constructor sortS (asUnifiedPattern (p sortS)))

{-|'binaryPattern' is a helper for building 'PatternM's for binary operators
like \and.
-}
binaryPattern
    :: (Sort Meta -> UnifiedPattern -> UnifiedPattern -> PatternMetaType)
    -> PatternM
    -> PatternM
    -> PatternM
binaryPattern constructor first second =
    case fillCheckPairSorts first second of
        Left (firstPattern, secondPattern) ->
            UnsortedPatternM
                (\sortS ->
                    constructor sortS (firstPattern sortS) (secondPattern sortS)
                )
        Right (commonSort, firstPattern, secondPattern) ->
            SortedPatternM
                { patternMPattern =
                    constructor commonSort firstPattern secondPattern
                , patternMSort    = commonSort
                }

newtype ChildSort = ChildSort (Sort Meta)
newtype ResultSort = ResultSort (Sort Meta)

{-|'binarySortedPattern' is a helper for building 'PatternM's for binary
operators where the result sort is different from the operand sort like \equals.
-}
binarySortedPattern
    :: (ResultSort
        -> ChildSort
        -> UnifiedPattern
        -> UnifiedPattern
        -> PatternMetaType)
    -> Maybe ChildSort
    -> PatternM
    -> PatternM
    -> PatternM
binarySortedPattern constructor maybeSort first second =
    case fillCheckPairSorts first second of
        Left (firstPattern, secondPattern) ->
            case maybeSort of
                Nothing ->
                    error
                        (  "Could not find a sort for equals children: "
                        ++ show (firstPattern dummySort)
                        ++ " and "
                        ++ show (secondPattern dummySort)
                        ++ "."
                        )
                Just childSort@(ChildSort s) ->
                    patternFromChildSort
                        (firstPattern s) (secondPattern s) childSort
        Right (commonSort, firstPattern, secondPattern) ->
            case maybeSort of
                Nothing ->
                    patternFromChildSort
                        firstPattern secondPattern (ChildSort commonSort)
                Just (ChildSort s) ->
                    if s == commonSort
                        then
                            patternFromChildSort
                                firstPattern
                                secondPattern
                                (ChildSort commonSort)
                        else
                            error
                                (  "Incompatible sorts for equals children: "
                                ++ show s
                                ++ " and "
                                ++ show commonSort
                                ++ "."
                                )
  where
    patternFromChildSort firstPattern secondPattern childSort =
        UnsortedPatternM
            (\sortS ->
                constructor (ResultSort sortS) childSort
                    firstPattern
                    secondPattern
            )

{-|'defineMetaSort' is a helper function for defining meta sorts together
with their constructors, helper functions and axioms.
-}
defineMetaSort
    :: String
    -> ( Sort Meta
       , Sort Meta
       , SentenceSymbol Meta
       , PatternM
       , SentenceSymbol Meta
       , [PatternM] -> PatternM
       , SentenceSymbol Meta
       , [PatternM] -> PatternM
       , SentenceSymbol Meta
       , [Sort Meta] -> [PatternM] -> PatternM
       , SentenceSymbol Meta
       , [PatternM] -> PatternM
       , [SentenceAxiom]
       )
defineMetaSort name =
    ( objectSort
    , listSort
    , emptyList
    , emptyListA
    , listConstructor
    , listConstructorA
    , append
    , appendA
    , inList
    , inListA
    , delete
    , deleteA
        -- inList
    ,   [ parameterizedAxiom [pS] (not_ (inListA [spS] [vs, emptyListA]))
        , parameterizedEqualsAxiom [pS]
            (inListA [spS] [vs, listConstructorA [vs', vS]])
            (or_
                (equalsS_ objectSort vs vs')
                (inListA [spS] [vs, vS])
            )
        -- append
        , equalsAxiom (appendA [emptyListA, vS]) vS
        , equalsAxiom
            (appendA [listConstructorA [vs, vS'], vS])
            (listConstructorA [vs, appendA [vS', vS]])
        -- delete
        , equalsAxiom
            (deleteA [vs, emptyListA])
            emptyListA
        , equalsAxiom
            (deleteA [vs, listConstructorA [vs', vS]])
            (or_
                (and_ (equalsS_ objectSort vs vs') (deleteA [vs, vS]))
                (and_
                    (not_ (equalsS_ objectSort vs vs'))
                    (listConstructorA [vs', deleteA [vs, vS]])
                )
            )
        ]
    )
  where
    objectSort = sort_ ("#" ++ name)
    listSort = sort_ ("#" ++ name ++ "List")
    emptyList = symbol_ ("#nil" ++ name ++ "List") [] listSort
    emptyListA = applyS emptyList []
    listConstructor =
        symbol_ ("#cons" ++ name ++ "List") [objectSort, listSort] listSort
    listConstructorA = applyS listConstructor
    append =
        symbol_ ("#append" ++ name ++ "List") [listSort, listSort] listSort
    appendA = applyS append
    inList =
        parameterizedSymbol_
            ("#in" ++ name ++ "List") [pS] [objectSort, listSort] spS
    inListA = applyPS inList
    delete =
        symbol_ ("#delete" ++ name ++ "List") [objectSort, listSort] listSort
    deleteA = applyS delete

sort_ :: String -> Sort Meta
sort_ name =
    SortActualSort SortActual
        { sortActualName = Id name
        , sortActualSorts = []
        }

str_ :: String -> PatternM
str_ s =
    SortedPatternM
        { patternMPattern = StringLiteralPattern (StringLiteral s)
        , patternMSort    = string'
        }

sortList_ :: [PatternM] -> PatternM
sortList_ = foldr (\p ps -> consSortListA [p, ps]) nilSortListA

patternList_ :: [PatternM] -> PatternM
patternList_ = foldr (\p ps -> consPatternListA [p, ps]) nilPatternListA

unparameterizedVariable_ :: String -> PatternM
unparameterizedVariable_ name =
    UnsortedPatternM
        (\sortS ->
            VariablePattern Variable
                { variableName = Id name
                , variableSort = sortS
                }
        )

stringVariable_ :: String -> Variable Meta
stringVariable_ name =
    Variable
        { variableName = Id name
        , variableSort = string'
        }

symbol_ :: String -> [Sort Meta] -> Sort Meta -> SentenceSymbol Meta
symbol_ name = parameterizedSymbol_ name []

parameterizedSymbol_
    :: String -> [SortVariable Meta] -> [Sort Meta] -> Sort Meta
    -> SentenceSymbol Meta
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

equalsS_ :: Sort Meta -> PatternM -> PatternM -> PatternM
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

equals_ :: PatternM -> PatternM -> PatternM
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

exists_ :: Variable Meta -> PatternM -> PatternM
exists_ variable1 =
    unaryPattern
        (\sortS pattern1 ->
            ExistsPattern Exists
                { existsSort     = sortS
                , existsVariable = variable1
                , existsChild    = pattern1
                }
        )

or_ :: PatternM -> PatternM -> PatternM
or_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            OrPattern Or
                { orSort   = commonSort
                , orFirst  = firstPattern
                , orSecond = secondPattern
                }
        )

and_ :: PatternM -> PatternM -> PatternM
and_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            AndPattern And
                { andSort   = commonSort
                , andFirst  = firstPattern
                , andSecond = secondPattern
                }
        )

implies_ :: PatternM -> PatternM -> PatternM
implies_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            ImpliesPattern Implies
                { impliesSort   = commonSort
                , impliesFirst  = firstPattern
                , impliesSecond = secondPattern
                }
        )

not_ :: PatternM -> PatternM
not_ =
    unaryPattern
        (\sortS pattern1 ->
            NotPattern Not
                { notSort   = sortS
                , notChild  = pattern1
                }
        )

pS = sortParameter "#sp"
spS = SortVariableSort pS

vf = unparameterizedVariable_ "#f"
vL = unparameterizedVariable_ "#L"
vphi = unparameterizedVariable_ "#phi"
vphi1 = unparameterizedVariable_ "#phi1"
vphi2 = unparameterizedVariable_ "#phi2"
vphi3 = unparameterizedVariable_ "#phi3"
vphii = unparameterizedVariable_ "#phii"
vpsi = unparameterizedVariable_ "#psi"
vR = unparameterizedVariable_ "#R"
vS = unparameterizedVariable_ "#S"
vS' = unparameterizedVariable_ "#S'"
vs = unparameterizedVariable_ "#s"
vs1 = unparameterizedVariable_ "#s1"
vs2 = unparameterizedVariable_ "#s2"
vs3 = unparameterizedVariable_ "#s3"
vs' = unparameterizedVariable_ "#s'"
vsigma = unparameterizedVariable_ "#sigma"
vu = unparameterizedVariable_ "#u"
v = unparameterizedVariable_ "#v"
v1 = unparameterizedVariable_ "#v1"
v2 = unparameterizedVariable_ "#v2"
vx = unparameterizedVariable_ "#x"
vx' = unparameterizedVariable_ "#x'"

( char', charList'
    , nilCharList, nilCharListA, consCharList, consCharListA
    , appendCharList, appendCharListA
    , inCharList, inCharListA
    , deleteCharList, deleteCharListA
    , charListAxioms
    )
  =
    defineMetaSort "Char"

( sort', sortList'
    , nilSortList, nilSortListA, consSortList, consSortListA
    , appendSortList, appendSortListA
    , inSortList, inSortListA
    , deleteSortList, deleteSortListA
    , sortListAxioms
    )
  =
    defineMetaSort "Sort"

( symbol', symbolList'
    , nilSymbolList, nilSymbolListA, consSymbolList, consSymbolListA
    , appendSymbolList, appendSymbolListA
    , inSymbolList, inSymbolListA
    , deleteSymbolList, deleteSymbolListA
    , symbolListAxioms
    )
  =
    defineMetaSort "Symbol"

( variable', variableList'
    , nilVariableList, nilVariableListA, consVariableList, consVariableListA
    , appendVariableList, appendVariableListA
    , inVariableList, inVariableListA
    , deleteVariableList, deleteVariableListA
    , variableListAxioms
    )
  =
    defineMetaSort "Variable"

( pattern', patternList'
    , nilPatternList, nilPatternListA, consPatternList, consPatternListA
    , appendPatternList, appendPatternListA
    , inPatternList, inPatternListA
    , deletePatternList, deletePatternListA
    , patternListAxioms
    )
  =
    defineMetaSort "Pattern"

string' = charList'

epsilon = symbol_ "#epsilon" [] string'
epsilonA = applyS epsilon []
epsilonAxiom = equalsAxiom epsilonA nilCharListA

sort = symbol_ "#sort" [string', sortList'] sort'

symbol = symbol_ "#symbol" [string', sortList', sortList', sort'] symbol'
symbolA = applyS symbol

getArgumentSorts = symbol_ "#getArgumentSorts" [symbol'] sortList'
getArgumentSortsA = applyS getArgumentSorts
getArgumentSortsAxiom =
    equalsAxiom (getArgumentSortsA [symbolA [vf, vS, vS', vs]]) vS'

getReturnSort = symbol_ "#getReturnSort" [symbol'] sort'
getReturnSortA = applyS getReturnSort
getReturnSortAxiom =
    equalsAxiom (getReturnSortA [symbolA [vf, vS, vS', vs]]) vs

variable = symbol_ "#variable" [string', sort'] variable'
variableA = applyS variable

applicationP = symbol_ "#application" [symbol', patternList'] pattern'
applicationA = applyS applicationP
andP = symbol_ "#\\and" [sort', pattern', pattern'] pattern'
andA = applyS andP
notP = symbol_ "#\\not" [sort', pattern'] pattern'
notA = applyS notP
existsP = symbol_ "#\\exists" [sort', variable', pattern'] pattern'
existsA = applyS existsP

variableAsPattern = symbol_ "#variableAsPattern" [variable'] pattern'
variableAsPatternA = applyS variableAsPattern
variableAsPatternAxiom =
    parameterizedAxiom
        [pS]
        (withSort spS
            (implies_
                (not_ (equalsS_ variable' v1 v2))
                (not_
                    (equals_
                        (variableAsPatternA [v1])
                        (variableAsPatternA [v2])
                    )
                )
            )
        )

variablePattern = symbol_ "#variablePattern" [string', sort'] pattern'
variablePatternA = applyS variablePattern
variablePatternAxiom =
    equalsAxiom
        (variablePatternA [vx, vs])
        (variableAsPatternA [variableA [vx, vs]])

orP = symbol_ "#\\or" [sort', pattern', pattern'] pattern'
orA = applyS orP
impliesP = symbol_ "#\\implies" [sort', pattern', pattern'] pattern'
impliesA = applyS impliesP
iffP = symbol_ "#\\iff" [sort', pattern', pattern'] pattern'
iffA = applyS iffP
forallP = symbol_ "#\\forall" [sort', variable', pattern'] pattern'
forallA = applyS forallP
ceilP = symbol_ "#\\ceil" [sort', sort', pattern'] pattern'
ceilA = applyS ceilP
floorP = symbol_ "#\\floor" [sort', sort', pattern'] pattern'
floorA = applyS floorP
equalsP = symbol_ "#\\equals" [sort', sort', pattern', pattern'] pattern'
equalsA = applyS equalsP
inP = symbol_ "#\\in" [sort', sort', pattern', pattern'] pattern'
inA = applyS inP
topP = symbol_ "#\\top" [sort'] pattern'
topA = applyS topP
bottomP = symbol_ "#\\bottom" [sort'] pattern'
bottomA = applyS bottomP

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

getFV = symbol_ "#getFV" [pattern'] variableList'
getFVA = applyS getFV
getFVFromPatterns = symbol_ "#getFVFromPatterns" [patternList'] variableList'
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

occursFree = parameterizedSymbol_ "#occursFree" [pS] [variable', pattern'] spS
occursFreeA = applyPS occursFree
occursFreeAxiom =
    parameterizedEqualsAxiom [pS]
        (occursFreeA [spS] [v, vphi])
        (inVariableListA [spS] [v, getFVA [vphi]])

freshName = symbol_ "#freshName" [patternList'] string'
freshNameA = applyS freshName
freshNameAxiom =
    parameterizedAxiom [pS]
        (not_
            (inVariableListA [spS]
                [variableA [freshNameA [vL], vs], getFVFromPatternsA [vL]]
            )
        )

substitute = symbol_ "#substitute" [pattern', pattern', variable'] pattern'
substituteA = applyS substitute
substitutePatterns =
    symbol_ "#substitutePatterns"
        [patternList', pattern', variable']
        patternList'
substitutePatternsA = applyS substitutePatterns

substitutePatternAxioms =
    [ equalsAxiom
        (substituteA [variableAsPatternA [vu], vpsi, v])
        (or_
            (and_ (equalsS_ variable' vu v) vpsi)
            (and_
                (not_ (equalsS_ variable' vu v))
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
    parameterizedAxiom [pS]
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

sortDeclared = parameterizedSymbol_ "#sortDeclared" [pS] [sort'] spS
sortDeclaredA = applyPS sortDeclared
symbolDeclared = parameterizedSymbol_ "#symbolDeclared" [pS] [symbol'] spS
symbolDeclaredA = applyPS symbolDeclared
axiomDeclared = parameterizedSymbol_ "#axiomDeclared" [pS] [pattern'] spS
axiomDeclaredA = applyPS axiomDeclared

sortsDeclared = parameterizedSymbol_ "#sortsDeclared" [pS] [sortList'] spS
sortsDeclaredA = applyPS sortsDeclared
sortsDeclaredAxioms =
    [ parameterizedAxiom [pS] (sortsDeclaredA [spS] [nilSortListA])
    , parameterizedEqualsAxiom [pS]
        (sortsDeclaredA [spS] [consSortListA [vs, vS]])
        (and_ (sortDeclaredA [spS] [vs]) (sortsDeclaredA [spS] [vS]))
    ]

ceilBTDeclaredAxiom =
    parameterizedAxiom [pS]
        (implies_
            (and_ (sortDeclaredA [spS] [vs1]) (sortDeclaredA [spS] [vs2]))
            (symbolDeclaredA [spS] [ceilBTA [vs1, vs2]])
        )

wellFormed = parameterizedSymbol_ "#wellFormed" [pS] [pattern'] spS
wellFormedA = applyPS wellFormed

wellFormedPatterns =
    parameterizedSymbol_ "#wellFormedPatterns" [pS] [patternList'] spS
wellFormedPatternsA = applyPS wellFormedPatterns
wellFormedPatternsAxioms =
    [ parameterizedAxiom [pS]
        (wellFormedPatternsA [spS] [nilPatternListA])
    , parameterizedEqualsAxiom [pS]
        (wellFormedPatternsA [spS] [consPatternListA [vphi, vL]])
        (and_ (wellFormedA [spS] [vphi]) (wellFormedPatternsA [spS] [vL]))
    ]

getSort = symbol_ "#getSort" [pattern'] sort'
getSortA = applyS getSort

getSortsFromPatterns = symbol_ "#getSortsFromPatterns" [patternList'] sortList'
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
            (wellFormedA [sort'] [variableAsPatternA [variableA [vx, vs]]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [applicationA [vsigma, vL]])
        (and_
            (wellFormedA [sort'] [applicationA [vsigma, vL]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [andA [vs, vphi, vpsi]])
        (and_
            (wellFormedA [sort'] [andA [vs, vphi, vpsi]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [notA [vs, vphi]])
        (and_
            (wellFormedA [sort'] [notA [vs, vphi]])
            vs
        )
    , parameterizedEqualsAxiom [pS]
        (getSortA [existsA [vs, v, vphi]])
        (and_
            (wellFormedA [sort'] [existsA [vs, v, vphi]])
            vs
        )
    ]

-- 7.7 Matching logic Proof System

provable = parameterizedSymbol_ "#provable" [pS] [pattern'] spS
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
    , parameterizedAxiom [pS]
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
        parameterizedAxiom [pS]
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
    , parameterizedAxiom [pS]
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
        parameterizedAxiom [pS]
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
        parameterizedAxiom [pS]
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
        parameterizedAxiom [pS]
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
        parameterizedAxiom [pS]
            (implies_
                (and_
                    (wellFormedA [spS] [variableAsPatternA [vu]])
                    (and_
                        (wellFormedA [spS] [variableAsPatternA [v]])
                        (wellFormedA [spS] [forallFormula])
                    )
                )
                (implies_
                    (not_ (equalsS_ variable' vu v))
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
        parameterizedAxiom [pS]
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
                        (not_ (equalsS_ variable' vu v))
                        (not_ (occursFreeA [spS] [vu, sigmaFormula vphii]))
                    )
                    (provableA [spS] [membershipFormula])
                )
            )
    ]

axiomAxiom =
    parameterizedAxiom [pS]
        (implies_
            (wellFormedA [spS] [vphi])
            (implies_
                (axiomDeclaredA [spS] [vphi])
                (provableA [spS] [vphi])
            )
        )

ceilBT = symbol_ "#`ceil" [sort', sort'] symbol'
ceilBTA = applyS ceilBT
ceilBTAxiom =
    equalsAxiom
        (ceilBTA [vs, vs'])
        (symbolA [str_ "ceil", sortList_ [vs, vs'], sortList_ [vs], vs'])

uncheckedKoreModule :: Module
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

uncheckedKoreDefinition :: Definition
uncheckedKoreDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = [uncheckedKoreModule]
        }

checkedKoreDefinition :: Either (Error VerifyError) Definition
checkedKoreDefinition = do
    verifyDefinition uncheckedKoreDefinition
    return uncheckedKoreDefinition

implicitKoreDefinition :: Definition
implicitKoreDefinition =
    case checkedKoreDefinition of
        Left err -> error (printError err)
        Right d  -> d

implicitKoreModule :: Module
implicitKoreModule =
    case checkedKoreDefinition of
        Left err                                   -> error (printError err)
        Right Definition {definitionModules = [m]} -> m
