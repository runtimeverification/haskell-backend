{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-|
Module      : Data.Kore.MetaML.Lift
Description : Lifts mixed 'Object' and 'Meta' constructs into pure 'Meta' ones.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Please refer to Section 9.2 (The Kore Language Semantics) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Data.Kore.MetaML.Lift ( liftModule
                             , liftSentence
                             , LiftableToMetaML(liftToMeta)
                             ) where

import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MLPatterns
import           Data.Kore.ASTTraversals
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.MetaML.AST

{-|'LiftableToMetaML' describes functionality to lift mixed Kore
'Object' and 'Meta' constructs to pure 'Meta' constructs.
-}
class LiftableToMetaML mixed where
    liftToMeta :: mixed -> CommonMetaPattern
    verbosityLiftToMeta :: Bool -> mixed -> CommonMetaPattern
    liftToMeta = verbosityLiftToMeta False

-- Section 9.2.1 Lift Object Identifiers to String Literals
instance LiftableToMetaML (Id Object) where
    verbosityLiftToMeta _ = Fix . StringLiteralPattern . StringLiteral . getId

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (SortVariable Object) where
    verbosityLiftToMeta _ sv = Fix $ VariablePattern Variable
        { variableName = Id $ ('#' :) $ getId $ getSortVariable sv
        , variableSort = sortMetaSort
        }

-- Section 9.2.2 Lift Object Sort Constructors to Meta Symbols
liftSortConstructor :: String -> Id Meta
liftSortConstructor name = Id ('#' : '`' : name)

-- Section 9.2.5 Lift Object Head Constructors to Meta Symbols
liftHeadConstructor :: String -> Id Meta
liftHeadConstructor = liftSortConstructor

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (SortActual Object) where
    verbosityLiftToMeta False sa = Fix $ apply
        (groundHead (liftSortConstructor (getId (sortActualName sa))))
        (fmap liftToMeta (sortActualSorts sa))
    verbosityLiftToMeta True sa = Fix $ apply sortHead
        [ liftToMeta (sortActualName sa)
        , verbosityLiftToMeta True (sortActualSorts sa)
        ]

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (Sort Object) where
    verbosityLiftToMeta verb (SortVariableSort sv) = verbosityLiftToMeta verb sv
    verbosityLiftToMeta verb (SortActualSort sv)   = verbosityLiftToMeta verb sv

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML [Sort Object] where
    verbosityLiftToMeta verb =
        foldr
            (applyConsSortList . verbosityLiftToMeta verb)
            nilSortListMetaPattern
      where
        applyConsSortList sort sortList =
            Fix $ apply consSortListHead [sort, sortList]

instance LiftableToMetaML [CommonMetaPattern] where
    verbosityLiftToMeta _ =
        foldr applyConsPatternList nilPatternListMetaPattern
      where
        applyConsPatternList pat patList =
            Fix $ apply consPatternListHead [pat, patList]

-- Section 9.2.8 Lift Patterns
instance LiftableToMetaML (Variable Object) where
    verbosityLiftToMeta verb v = Fix $ apply variableHead
        [ verbosityLiftToMeta verb (variableName v)
        , verbosityLiftToMeta verb (variableSort v)]

-- Section 9.2.8 Lift Patterns
instance LiftableToMetaML UnifiedPattern where
    verbosityLiftToMeta verb = bottomUpVisitor (liftReducer verb)

liftReducer
    :: MetaOrObject level
    => Bool
    -> Pattern level Variable CommonMetaPattern
    -> CommonMetaPattern
liftReducer verb p = applyMetaObjectFunction
    (PatternObjectMeta p)
    MetaOrObjectTransformer
        { objectTransformer =
            liftObjectReducer verb . getPatternObjectMeta
        , metaTransformer = Fix . getPatternObjectMeta
        }

liftObjectReducer
    :: Bool
    -> Pattern Object Variable CommonMetaPattern
    -> CommonMetaPattern
liftObjectReducer verb p = case p of
    AndPattern ap -> Fix $ apply (metaMLPatternHead AndPatternType)
        (verbosityLiftToMeta verb (andSort ap) : getPatternChildren ap)
    ApplicationPattern ap -> let sa = applicationSymbolOrAlias ap in
        Fix $ apply
            (groundHead
                (liftHeadConstructor (getId (symbolOrAliasConstructor sa))))
            (map (verbosityLiftToMeta verb) (symbolOrAliasParams sa)
                ++ applicationChildren ap)
    BottomPattern bp -> Fix $ apply (metaMLPatternHead BottomPatternType)
        [verbosityLiftToMeta verb (bottomSort bp)]
    CeilPattern cp -> Fix $ apply (metaMLPatternHead CeilPatternType)
        [ verbosityLiftToMeta verb (ceilOperandSort cp)
        , verbosityLiftToMeta verb (ceilResultSort cp)
        , ceilChild cp
        ]
    DomainValuePattern dvp ->
        Fix $ apply (metaMLPatternHead DomainValuePatternType)
            [ verbosityLiftToMeta verb (domainValueSort dvp)
            , domainValueChild dvp
            ]
    EqualsPattern cp -> Fix $ apply (metaMLPatternHead EqualsPatternType)
        [ verbosityLiftToMeta verb (equalsOperandSort cp)
        , verbosityLiftToMeta verb (equalsResultSort cp)
        , equalsFirst cp
        , equalsSecond cp
        ]
    ExistsPattern ep -> Fix $ apply (metaMLPatternHead ExistsPatternType)
        [ verbosityLiftToMeta verb (existsSort ep)
        , verbosityLiftToMeta verb (existsVariable ep)
        , existsChild ep
        ]
    FloorPattern cp -> Fix $ apply (metaMLPatternHead FloorPatternType)
        [ verbosityLiftToMeta verb (floorOperandSort cp)
        , verbosityLiftToMeta verb (floorResultSort cp)
        , floorChild cp
        ]
    ForallPattern ep -> Fix $ apply (metaMLPatternHead ForallPatternType)
        [ verbosityLiftToMeta verb (forallSort ep)
        , verbosityLiftToMeta verb (forallVariable ep)
        , forallChild ep
        ]
    IffPattern ap -> Fix $ apply (metaMLPatternHead IffPatternType)
        (verbosityLiftToMeta verb (iffSort ap) : getPatternChildren ap)
    ImpliesPattern ap -> Fix $ apply (metaMLPatternHead ImpliesPatternType)
        (verbosityLiftToMeta verb (impliesSort ap) : getPatternChildren ap)
    InPattern ap -> Fix $ apply (metaMLPatternHead InPatternType)
        [ verbosityLiftToMeta verb (inOperandSort ap)
        , verbosityLiftToMeta verb (inResultSort ap)
        , inContainedChild ap
        , inContainingChild ap
        ]
    NextPattern ap -> Fix $ apply (metaMLPatternHead NextPatternType)
        [verbosityLiftToMeta verb (nextSort ap), nextChild ap]
    NotPattern ap -> Fix $ apply (metaMLPatternHead NotPatternType)
        [verbosityLiftToMeta verb (notSort ap), notChild ap]
    OrPattern ap -> Fix $ apply (metaMLPatternHead OrPatternType)
        (verbosityLiftToMeta verb (orSort ap) : getPatternChildren ap)
    RewritesPattern ap -> Fix $ apply (metaMLPatternHead RewritesPatternType)
        (verbosityLiftToMeta verb (rewritesSort ap) : getPatternChildren ap)
    TopPattern bp -> Fix $ apply (metaMLPatternHead TopPatternType)
        [verbosityLiftToMeta verb (topSort bp)]

liftAttributes :: KoreAttributes -> MetaAttributes
liftAttributes (Attributes as) =
    Attributes (map liftToMeta as)

-- Section 9.2.4 Lift Sort Declarations
liftSortDeclaration
    :: KoreSentenceSort
    -> (MetaSentenceSymbol, MetaSentenceAxiom, MetaSentenceAxiom)
liftSortDeclaration ss =
    (symbolDeclaration, helperFunctionAxiom, declaredAxiom)
  where
    sortName = sentenceSortName ss
    sortParameters = sentenceSortParameters ss
    sortParametersAsSorts = map SortVariableSort sortParameters
    symbolId = liftSortConstructor (getId sortName)
    symbolDeclaration = SentenceSymbol
        { sentenceSymbolSymbol = groundSymbol symbolId
        , sentenceSymbolSorts = map (const sortMetaSort) sortParameters
        , sentenceSymbolResultSort = sortMetaSort
        , sentenceSymbolAttributes = Attributes []
        }
    sortParam = SortVariable (Id "#s")
    sortParamAsSort = SortVariableSort sortParam
    actualSort = SortActual
        { sortActualName = sortName
        , sortActualSorts = sortParametersAsSorts
        }
    helperFunctionAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = Fix $ EqualsPattern Equals
            { equalsOperandSort = sortMetaSort
            , equalsResultSort = sortParamAsSort
            , equalsFirst = verbosityLiftToMeta False actualSort
            , equalsSecond = verbosityLiftToMeta True actualSort
            }
        }
    declaredAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = Fix $ ImpliesPattern Implies
            { impliesSort = SortVariableSort sortParam
            , impliesFirst = Fix $ apply (sortsDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False sortParametersAsSorts]
            , impliesSecond = Fix $ apply (sortDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False actualSort]
            }
        }

-- Section 9.2.6 Lift Object Symbol Declarations
liftSymbolDeclaration
    :: KoreSentenceSymbol Object
    -> (MetaSentenceSymbol, MetaSentenceAxiom, MetaSentenceAxiom)
liftSymbolDeclaration sd =
    (symbolOrAliasLiftedDeclaration sd, helperFunctionAxiom, declaredAxiom)
  where
    symbol = sentenceSymbolSymbol sd
    sortParameters = symbolParams symbol
    sortParametersAsSorts = map SortVariableSort sortParameters
    sorts = sentenceSymbolSorts sd
    patternSorts = map (const patternMetaSort) sorts
    symbolName = symbolConstructor symbol
    liftedSymbolId = liftHeadConstructor (getId symbolName)
    sigma = Fix $ apply symbolHead
        [ liftToMeta symbolName
        , liftToMeta sortParametersAsSorts
        , liftToMeta sorts
        , liftToMeta (sentenceSymbolResultSort sd)
        ]
    freshVariable n s = Fix $ VariablePattern Variable
        { variableName = Id ("#P" ++ show (n::Int))
        , variableSort = s
        }
    phis = zipWith freshVariable [1..] patternSorts
    sortParam = SortVariable (Id "#s")
    sortParamAsSort = SortVariableSort sortParam
    helperFunctionAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = Fix $ EqualsPattern Equals
            { equalsOperandSort = patternMetaSort
            , equalsResultSort = sortParamAsSort
            , equalsFirst = Fix $ apply (groundHead liftedSymbolId)
                (map liftToMeta sortParametersAsSorts ++ phis)
            , equalsSecond = Fix $ apply applicationHead
                [ sigma, liftToMeta phis]
            }
        }
    declaredAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = Fix $ ImpliesPattern Implies
            { impliesSort = SortVariableSort sortParam
            , impliesFirst = Fix $ apply (sortsDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False sortParametersAsSorts]
            , impliesSecond = Fix $ apply (symbolDeclaredHead sortParamAsSort)
                [sigma]
            }
        }

symbolOrAliasLiftedDeclaration
    :: SentenceSymbolOrAlias sa
    => sa attributes Object
    -> MetaSentenceSymbol
symbolOrAliasLiftedDeclaration sa = symbolDeclaration
  where
    sortParameters = getSentenceSymbolOrAliasSortParams sa
    sorts = getSentenceSymbolOrAliasArgumentSorts sa
    patternSorts = map (const patternMetaSort) sorts
    aliasName = getSentenceSymbolOrAliasConstructor sa
    liftedSymbolId = liftHeadConstructor (getId aliasName)
    symbolDeclaration = SentenceSymbol
        { sentenceSymbolSymbol = groundSymbol liftedSymbolId
        , sentenceSymbolSorts =
            map (const sortMetaSort) sortParameters ++
            patternSorts
        , sentenceSymbolResultSort = patternMetaSort
        , sentenceSymbolAttributes = Attributes []
        }

-- Section 9.2.7 Lift Object Alias Declarations
liftAliasDeclaration :: KoreSentenceAlias Object -> MetaSentenceSymbol
liftAliasDeclaration = symbolOrAliasLiftedDeclaration

{-|'liftSentence' transforms a 'Sentence' in one or more 'MetaSentences'
encoding it.
-}
liftSentence :: Sentence -> [MetaSentence]
liftSentence (MetaSentenceAliasSentence msa) =
    [ AliasMetaSentence msa
        { sentenceAliasAttributes = liftAttributes (sentenceAliasAttributes msa)
        }
    ]
liftSentence (ObjectSentenceAliasSentence osa) =
    [ SymbolMetaSentence (liftAliasDeclaration osa)]
liftSentence (MetaSentenceSymbolSentence mss) =
    [ SymbolMetaSentence mss
        { sentenceSymbolAttributes =
            liftAttributes (sentenceSymbolAttributes mss)
        }
    ]
liftSentence (ObjectSentenceSymbolSentence oss) =
    let (mss, axiom1, axiom2) = liftSymbolDeclaration oss in
        [ SymbolMetaSentence mss
        , AxiomMetaSentence axiom1
        , AxiomMetaSentence axiom2
        ]
liftSentence (SentenceSortSentence ss) =
    let (mss, axiom1, axiom2) = liftSortDeclaration ss in
        [ SymbolMetaSentence mss
        , AxiomMetaSentence axiom1
        , AxiomMetaSentence axiom2
        ]
liftSentence (SentenceAxiomSentence as) =
    [ AxiomMetaSentence SentenceAxiom
        { sentenceAxiomParameters = metaParameters
        , sentenceAxiomAttributes = liftAttributes (sentenceAxiomAttributes as)
        , sentenceAxiomPattern =
            if null objectParameters
                then liftedPattern
                else undefined
        }
    ]
  where
    metaParameters =
        [sv | MetaSortVariable sv <- sentenceAxiomParameters as]
    objectParameters =
        [sv | ObjectSortVariable sv <- sentenceAxiomParameters as]
    liftedPattern = liftToMeta (sentenceAxiomPattern as)
liftSentence (SentenceImportSentence is) =
    [ ImportMetaSentence is
        { sentenceImportAttributes =
            liftAttributes (sentenceImportAttributes is)
        }
    ]

liftModule :: KoreModule -> MetaModule
liftModule m = Module
    { moduleName = moduleName m
    , moduleAttributes = liftAttributes (moduleAttributes m)
    , moduleSentences = concatMap liftSentence (moduleSentences m)
    }
