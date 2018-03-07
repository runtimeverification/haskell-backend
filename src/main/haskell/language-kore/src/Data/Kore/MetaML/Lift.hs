{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.MetaML.Lift where

import           Data.Fix

import           Data.Kore.AST
import           Data.Kore.ASTTraversals
import           Data.Kore.ImplicitDefinitions
import           Data.Kore.MetaML.AST

class LiftableToMetaML mixed where
    liftToMeta :: mixed -> MetaMLPattern Variable
    verbosityLiftToMeta :: Bool -> mixed -> MetaMLPattern Variable
    liftToMeta = verbosityLiftToMeta False

instance LiftableToMetaML (Id Object) where
    verbosityLiftToMeta _ = Fix . StringLiteralPattern . StringLiteral . getId

instance LiftableToMetaML (SortVariable Object) where
    verbosityLiftToMeta _ sv = Fix $ VariablePattern Variable
        { variableName = Id $ ('#' :) $ getId $ getSortVariable sv
        , variableSort = sortMetaSort
        }

liftSortConstructor :: String -> Id Meta
liftSortConstructor name = Id ('#' : '`' : name)

liftHeadConstructor :: String -> Id Meta
liftHeadConstructor = liftSortConstructor

instance LiftableToMetaML (SortActual Object) where
    verbosityLiftToMeta False sa = Fix $ apply
        (groundHead (liftSortConstructor (getId (sortActualName sa))))
        (fmap liftToMeta (sortActualSorts sa))
    verbosityLiftToMeta True sa = Fix $ apply sortHead
        [ liftToMeta (sortActualName sa)
        , verbosityLiftToMeta True (sortActualSorts sa)
        ]

instance LiftableToMetaML (Sort Object) where
    verbosityLiftToMeta verb (SortVariableSort sv) = verbosityLiftToMeta verb sv
    verbosityLiftToMeta verb (SortActualSort sv)   = verbosityLiftToMeta verb sv

instance LiftableToMetaML [Sort Object] where
    verbosityLiftToMeta verb = foldr (applyConsSortList . verbosityLiftToMeta verb) nilSortListMetaPattern
      where
        applyConsSortList sort sortList =
            Fix $ apply consSortListHead [sort, sortList]

instance LiftableToMetaML [MetaMLPattern Variable] where
    verbosityLiftToMeta _ =
        foldr applyConsPatternList nilPatternListMetaPattern
      where
        applyConsPatternList pat patList =
            Fix $ apply consPatternListHead [pat, patList]

instance LiftableToMetaML (Variable Object) where
    verbosityLiftToMeta verb v = Fix $ apply variableHead
        [ verbosityLiftToMeta verb (variableName v)
        , verbosityLiftToMeta verb (variableSort v)]

instance LiftableToMetaML UnifiedPattern where
    verbosityLiftToMeta verb = bottomUpVisitor liftReducer
      where
        liftReducer p = applyMetaObjectFunction
            (PatternObjectMeta p)
            (liftObjectReducer verb . getPatternObjectMeta)
            (Fix . getPatternObjectMeta)

liftObjectReducer
    :: Bool
    -> Pattern Object Variable (MetaMLPattern Variable)
    -> MetaMLPattern Variable
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

liftSortDeclaration
    :: SentenceSort
    -> (SentenceSymbol Meta, MetaSentenceAxiom, MetaSentenceAxiom)
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
    helperFunctionAxiom = MetaSentenceAxiom
        { metaSentenceAxiomAttributes = Attributes []
        , metaSentenceAxiomParameters = [sortParam]
        , metaSentenceAxiomPattern = Fix $ EqualsPattern Equals
            { equalsOperandSort = sortMetaSort
            , equalsResultSort = sortParamAsSort
            , equalsFirst = verbosityLiftToMeta False actualSort
            , equalsSecond = verbosityLiftToMeta True actualSort
            }
        }
    declaredAxiom = MetaSentenceAxiom
        { metaSentenceAxiomAttributes = Attributes []
        , metaSentenceAxiomParameters = [sortParam]
        , metaSentenceAxiomPattern = Fix $ ImpliesPattern Implies
            { impliesSort = SortVariableSort sortParam
            , impliesFirst = Fix $ apply (sortsDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False sortParametersAsSorts]
            , impliesSecond = Fix $ apply (sortDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False actualSort]
            }
        }

liftSymbolDeclaration
    :: SentenceSymbol Object
    -> (SentenceSymbol Meta, MetaSentenceAxiom, MetaSentenceAxiom)
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
    helperFunctionAxiom = MetaSentenceAxiom
        { metaSentenceAxiomAttributes = Attributes []
        , metaSentenceAxiomParameters = [sortParam]
        , metaSentenceAxiomPattern = Fix $ EqualsPattern Equals
            { equalsOperandSort = patternMetaSort
            , equalsResultSort = sortParamAsSort
            , equalsFirst = Fix $ apply (groundHead liftedSymbolId)
                (map liftToMeta sortParametersAsSorts ++ phis)
            , equalsSecond = Fix $ apply applicationHead
                [ sigma, liftToMeta phis]
            }
        }
    declaredAxiom = MetaSentenceAxiom
        { metaSentenceAxiomAttributes = Attributes []
        , metaSentenceAxiomParameters = [sortParam]
        , metaSentenceAxiomPattern = Fix $ ImpliesPattern Implies
            { impliesSort = SortVariableSort sortParam
            , impliesFirst = Fix $ apply (sortsDeclaredHead sortParamAsSort)
                [verbosityLiftToMeta False sortParametersAsSorts]
            , impliesSecond = Fix $ apply (symbolDeclaredHead sortParamAsSort)
                [sigma]
            }
        }

symbolOrAliasLiftedDeclaration
    :: SentenceSymbolOrAlias sa
    => sa Object
    -> SentenceSymbol Meta
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

liftAliasDeclaration :: SentenceAlias Object -> SentenceSymbol Meta
liftAliasDeclaration = symbolOrAliasLiftedDeclaration

liftSentence :: Sentence -> [MetaSentence]
liftSentence (MetaSentenceAliasSentence msa) =
    [ AliasMetaSentence msa ]
liftSentence (ObjectSentenceAliasSentence osa) =
    [ SymbolMetaSentence (liftAliasDeclaration osa)]
liftSentence (MetaSentenceSymbolSentence mss) =
    [ SymbolMetaSentence mss ]
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
    [ AxiomMetaSentence MetaSentenceAxiom
        { metaSentenceAxiomParameters = metaParameters
        , metaSentenceAxiomAttributes = sentenceAxiomAttributes as
        , metaSentenceAxiomPattern = liftToMeta (sentenceAxiomPattern as)
        }
    ]
  where
    metaParameters = [sv | MetaSortVariable sv <- sentenceAxiomParameters as]
liftSentence (SentenceImportSentence is) = [ImportMetaSentence is]

liftModule :: Module -> MetaModule
liftModule m = MetaModule
    { metaModuleName = moduleName m
    , metaModuleAttributes = moduleAttributes m
    , metaModuleSentences = concatMap liftSentence (moduleSentences m)
    }
