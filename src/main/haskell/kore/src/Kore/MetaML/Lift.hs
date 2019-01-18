{-|
Module      : Kore.MetaML.Lift
Description : Lifts mixed 'Object' and 'Meta' constructs into pure 'Meta' ones.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Please refer to Section 9.2 (The Kore Language Semantics) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.MetaML.Lift
    ( liftDefinition
    , liftModule
    , liftSentence
    , LiftableToMetaML(liftToMeta)
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Functor.Foldable as Recursive
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Kore
import           Kore.AST.MLPatterns
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Implicit.ImplicitSorts
import           Kore.MetaML.AST

{-|'LiftableToMetaML' describes functionality to lift mixed Kore
'Object' and 'Meta' constructs to pure 'Meta' constructs.
-}
class LiftableToMetaML mixed where
    liftToMeta :: mixed -> CommonMetaPattern

{-|'VerboseLiftableToMetaML' describes functionality to verbosely
lift mixed Kore 'Object' and 'Meta' constructs to pure 'Meta' constructs.
-}
class VerboseLiftableToMetaML mixed where
    verboseLiftToMeta :: mixed -> CommonMetaPattern

-- Section 9.2.1 Lift Object Identifiers to String Literals
instance LiftableToMetaML (Id Object) where
    liftToMeta =
        asCommonMetaPattern
        . StringLiteralPattern
        . StringLiteral
        . getId

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (SortVariable Object) where
    liftToMeta sv = asCommonMetaPattern $ VariablePattern Variable
        { variableName = Id
            { getId = Text.cons '#' $ getId $ getSortVariable sv
            , idLocation = AstLocationLifted $ idLocation $ getSortVariable sv
            }
        , variableSort = sortMetaSort
        }

-- Section 9.2.2 Lift Object Sort Constructors to Meta Symbols
liftSortConstructor :: Text -> Text
liftSortConstructor name = "#`" <> name

-- Section 9.2.5 Lift Object Head Constructors to Meta Symbols
liftHeadConstructor :: Text -> Text
liftHeadConstructor = liftSortConstructor

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (SortActual Object) where
    liftToMeta sa = App_
        (groundHead
            (liftSortConstructor (getId sortId))
            (AstLocationLifted (idLocation sortId))
        )
        (fmap liftToMeta (sortActualSorts sa))
      where
        sortId = sortActualName sa

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance VerboseLiftableToMetaML (SortActual Object) where
    verboseLiftToMeta sa =
        App_ sortHead
            [ liftToMeta (sortActualName sa)
            , verboseLiftToMeta (sortActualSorts sa)
            ]

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
instance LiftableToMetaML (Sort Object) where
    liftToMeta (SortVariableSort sv) = liftToMeta sv
    liftToMeta (SortActualSort sv)   = liftToMeta sv

instance VerboseLiftableToMetaML (Sort Object) where
    verboseLiftToMeta (SortVariableSort sv) = liftToMeta sv
    verboseLiftToMeta (SortActualSort sa)   = verboseLiftToMeta sa

-- Section 9.2.3 Lift Object Sorts and Object Sort Lists
liftSortListToMeta
    :: (Sort Object -> CommonMetaPattern)
    -> ([Sort Object] -> CommonMetaPattern)
liftSortListToMeta sortLifter =
    foldr
        (applyConsSortList . sortLifter)
        nilSortListMetaPattern
  where
    applyConsSortList sort sortList =
        App_ consSortListHead [sort, sortList]

instance VerboseLiftableToMetaML [Sort Object] where
    verboseLiftToMeta = liftSortListToMeta verboseLiftToMeta

instance LiftableToMetaML [Sort Object] where
    liftToMeta = liftSortListToMeta liftToMeta

instance LiftableToMetaML [CommonMetaPattern] where
    liftToMeta =
        foldr applyConsPatternList nilPatternListMetaPattern
      where
        applyConsPatternList pat patList =
            App_ consPatternListHead [pat, patList]

-- Section 9.2.8 Lift Patterns
instance LiftableToMetaML (Variable Object) where
    liftToMeta v = App_ variableHead
        [ liftToMeta (variableName v)
        , liftToMeta (variableSort v)]

-- Section 9.2.8 Lift Patterns
instance LiftableToMetaML CommonKorePattern where
    liftToMeta = Recursive.fold (liftReducer . Cofree.tailF)

liftReducer
    :: UnifiedPattern Domain.Builtin Variable CommonMetaPattern
    -> CommonMetaPattern
liftReducer =
    \case
        UnifiedMetaPattern metaP -> asCommonMetaPattern metaP
        UnifiedObjectPattern objectP -> liftObjectReducer objectP

liftObjectReducer
    :: Pattern Object Domain.Builtin Variable CommonMetaPattern
    -> CommonMetaPattern
liftObjectReducer p = case p of
    AndPattern ap -> applyMetaMLPatternHead AndPatternType
        (liftToMeta (andSort ap) : getPatternChildren ap)
    ApplicationPattern ap ->
        let
            sa = applicationSymbolOrAlias ap
            saId = symbolOrAliasConstructor sa
        in
        App_
            (groundHead
                (liftHeadConstructor (getId saId))
                (AstLocationLifted (idLocation saId))
            )
            (map liftToMeta (symbolOrAliasParams sa)
                ++ applicationChildren ap)
    BottomPattern bp -> applyMetaMLPatternHead BottomPatternType
        [liftToMeta (bottomSort bp)]
    CeilPattern cp -> applyMetaMLPatternHead CeilPatternType
        [ liftToMeta (ceilOperandSort cp)
        , liftToMeta (ceilResultSort cp)
        , ceilChild cp
        ]
    DomainValuePattern dvp ->
        applyMetaMLPatternHead DomainValuePatternType
            [ liftToMeta (domainValueSort dvp)
            , mempty <$ Builtin.asMetaPattern (domainValueChild dvp)
            ]
    EqualsPattern cp -> applyMetaMLPatternHead EqualsPatternType
        [ liftToMeta (equalsOperandSort cp)
        , liftToMeta (equalsResultSort cp)
        , equalsFirst cp
        , equalsSecond cp
        ]
    ExistsPattern ep -> applyMetaMLPatternHead ExistsPatternType
        [ liftToMeta (existsSort ep)
        , liftToMeta (existsVariable ep)
        , existsChild ep
        ]
    FloorPattern cp -> applyMetaMLPatternHead FloorPatternType
        [ liftToMeta (floorOperandSort cp)
        , liftToMeta (floorResultSort cp)
        , floorChild cp
        ]
    ForallPattern ep -> applyMetaMLPatternHead ForallPatternType
        [ liftToMeta (forallSort ep)
        , liftToMeta (forallVariable ep)
        , forallChild ep
        ]
    IffPattern ap -> applyMetaMLPatternHead IffPatternType
        (liftToMeta (iffSort ap) : getPatternChildren ap)
    ImpliesPattern ap -> applyMetaMLPatternHead ImpliesPatternType
        (liftToMeta (impliesSort ap) : getPatternChildren ap)
    InPattern ap -> applyMetaMLPatternHead InPatternType
        [ liftToMeta (inOperandSort ap)
        , liftToMeta (inResultSort ap)
        , inContainedChild ap
        , inContainingChild ap
        ]
    NextPattern ap -> applyMetaMLPatternHead NextPatternType
        [liftToMeta (nextSort ap), nextChild ap]
    NotPattern ap -> applyMetaMLPatternHead NotPatternType
        [liftToMeta (notSort ap), notChild ap]
    OrPattern ap -> applyMetaMLPatternHead OrPatternType
        (liftToMeta (orSort ap) : getPatternChildren ap)
    RewritesPattern ap -> applyMetaMLPatternHead RewritesPatternType
        (liftToMeta (rewritesSort ap) : getPatternChildren ap)
    TopPattern bp -> applyMetaMLPatternHead TopPatternType
        [liftToMeta (topSort bp)]
    VariablePattern vp ->
        App_ variableAsPatternHead [liftToMeta vp]
  where
    applyMetaMLPatternHead patternType =
        App_
            (metaMLPatternHead
                patternType
                (AstLocationLifted AstLocationImplicit)
            )

-- Section 9.2.4 Lift Sort Declarations
liftSortDeclaration
    :: KoreSentenceSort Object
    -> (MetaSentenceSymbol, MetaSentenceAxiom, MetaSentenceAxiom)
liftSortDeclaration ss =
    (symbolDeclaration, helperFunctionAxiom, declaredAxiom)
  where
    sortName = sentenceSortName ss
    sortParameters = sentenceSortParameters ss
    sortParametersAsSorts = map SortVariableSort sortParameters
    symbolId = liftSortConstructor (getId sortName)
    liftedSymbolLocation = AstLocationLifted (idLocation sortName)
    symbolDeclaration = SentenceSymbol
        { sentenceSymbolSymbol = groundSymbol (Id symbolId liftedSymbolLocation)
        , sentenceSymbolSorts = map (const sortMetaSort) sortParameters
        , sentenceSymbolResultSort = sortMetaSort
        , sentenceSymbolAttributes = Attributes []
        }
    sortParam = SortVariable (Id "#s" liftedSymbolLocation)
    sortParamAsSort = SortVariableSort sortParam
    actualSort = SortActualSort SortActual
        { sortActualName = sortName
        , sortActualSorts = sortParametersAsSorts
        }
    helperFunctionAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = asCommonMetaPattern . EqualsPattern
            $ Equals
                { equalsOperandSort = sortMetaSort
                , equalsResultSort = sortParamAsSort
                , equalsFirst = liftToMeta actualSort
                , equalsSecond = verboseLiftToMeta actualSort
                }
        }
    declaredAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = asCommonMetaPattern . ImpliesPattern
            $ Implies
                { impliesSort = SortVariableSort sortParam
                , impliesFirst = App_ (sortsDeclaredHead sortParamAsSort)
                    [liftToMeta sortParametersAsSorts]
                , impliesSecond = App_ (sortDeclaredHead sortParamAsSort)
                    [liftToMeta actualSort]
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
    liftedSymbolLocation = AstLocationLifted (idLocation symbolName)
    sigma = App_ symbolHead
        [ liftToMeta symbolName
        , liftToMeta sortParametersAsSorts
        , liftToMeta sorts
        , liftToMeta (sentenceSymbolResultSort sd)
        ]
    freshVariable n s = asCommonMetaPattern $ VariablePattern Variable
        { variableName = Id ("#P" <> (Text.pack . show) (n::Int)) liftedSymbolLocation
        , variableSort = s
        }
    phis = zipWith freshVariable [1..] patternSorts
    sortParam = SortVariable (Id "#s" liftedSymbolLocation)
    sortParamAsSort = SortVariableSort sortParam
    helperFunctionAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = asCommonMetaPattern . EqualsPattern
            $ Equals
                { equalsOperandSort = patternMetaSort
                , equalsResultSort = sortParamAsSort
                , equalsFirst =
                    App_ (groundHead liftedSymbolId liftedSymbolLocation)
                        (map liftToMeta sortParametersAsSorts ++ phis)
                , equalsSecond = App_ applicationHead
                    [ sigma, liftToMeta phis]
                }
        }
    declaredAxiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [sortParam]
        , sentenceAxiomPattern = asCommonMetaPattern . ImpliesPattern
            $ Implies
                { impliesSort = SortVariableSort sortParam
                , impliesFirst = App_ (sortsDeclaredHead sortParamAsSort)
                    [liftToMeta sortParametersAsSorts]
                , impliesSecond =
                    App_ (symbolDeclaredHead sortParamAsSort) [sigma]
                }
        }

symbolOrAliasLiftedDeclaration
    :: SentenceSymbolOrAlias sa
    => sa Object pat
    -> MetaSentenceSymbol
symbolOrAliasLiftedDeclaration sa = symbolDeclaration
  where
    sortParameters = getSentenceSymbolOrAliasSortParams sa
    sorts = getSentenceSymbolOrAliasArgumentSorts sa
    patternSorts = map (const patternMetaSort) sorts
    aliasName = getSentenceSymbolOrAliasConstructor sa
    liftedSymbolId = liftHeadConstructor (getId aliasName)
    liftedSymbolLocation = AstLocationLifted (idLocation aliasName)
    symbolDeclaration = SentenceSymbol
        { sentenceSymbolSymbol =
            groundSymbol Id
                { getId = liftedSymbolId
                , idLocation = liftedSymbolLocation
                }
        , sentenceSymbolSorts =
            map (const sortMetaSort) sortParameters ++
            patternSorts
        , sentenceSymbolResultSort = patternMetaSort
        , sentenceSymbolAttributes = Attributes []
        }

-- Section 9.2.7 Lift Object Alias Declarations
liftAliasDeclaration
    :: KoreSentenceAlias Object
    -> (MetaSentenceSymbol, MetaSentenceAxiom)
liftAliasDeclaration as = (symbolOrAliasLiftedDeclaration as, axiom)
  where
    axiom = SentenceAxiom
        { sentenceAxiomAttributes = Attributes []
        , sentenceAxiomParameters = [ sortParam ]
        , sentenceAxiomPattern    = pat
        }
    pat = asCommonMetaPattern . EqualsPattern $
        Equals
            { equalsOperandSort = patternMetaSort
            , equalsResultSort  = SortVariableSort sortParam
            , equalsFirst       = left
            , equalsSecond      = right
            }
    SentenceAlias { sentenceAliasLeftPattern } = as
    SentenceAlias { sentenceAliasRightPattern } = as
    left =
        liftToMeta
        $ (asCommonKorePattern . ApplicationPattern)
        $ fmap (asCommonKorePattern . VariablePattern) sentenceAliasLeftPattern
    right = liftToMeta sentenceAliasRightPattern
    sortParam = SortVariable (Id "#s" liftedSymbolLocation)
    sortName = (aliasConstructor . sentenceAliasAlias) as
    liftedSymbolLocation = AstLocationLifted (idLocation sortName)

{-|'liftSentence' transforms a 'Sentence' in one or more 'MetaSentences'
encoding it.
-}
liftSentence :: KoreSentence -> [MetaSentence]
liftSentence = applyUnifiedSentence liftMetaSentence liftObjectSentence

liftMetaSentence
    :: Sentence Meta UnifiedSortVariable CommonKorePattern
    -> [MetaSentence]
liftMetaSentence (SentenceAliasSentence msa) =
    [ SentenceAliasSentence msa
        { sentenceAliasAttributes = sentenceAliasAttributes msa
        , sentenceAliasLeftPattern = sentenceAliasLeftPattern msa
        , sentenceAliasRightPattern = liftToMeta (sentenceAliasRightPattern msa)
        }
    ]
liftMetaSentence (SentenceSymbolSentence mss) =
    [ SentenceSymbolSentence mss
        { sentenceSymbolAttributes =
            sentenceSymbolAttributes mss
        }
    ]
liftMetaSentence (SentenceSortSentence mss) =
    [ SentenceSortSentence mss
        { sentenceSortName = sentenceSortName mss
        , sentenceSortParameters = sentenceSortParameters mss
        , sentenceSortAttributes = sentenceSortAttributes mss
        }
    ]
liftMetaSentence (SentenceAxiomSentence as) =
    liftMetaSentenceClaimOrAxiom SentenceAxiomSentence as
liftMetaSentence (SentenceClaimSentence as) =
    liftMetaSentenceClaimOrAxiom SentenceClaimSentence as
liftMetaSentence (SentenceImportSentence is) =
    [ SentenceImportSentence is
        { sentenceImportAttributes =
            sentenceImportAttributes is
        }
    ]

liftMetaSentenceClaimOrAxiom
    ::  (  forall param pat
        .  SentenceAxiom param pat
        -> Sentence Meta param pat
        )
    -> SentenceAxiom (Unified SortVariable) CommonKorePattern
    -> [MetaSentence]
liftMetaSentenceClaimOrAxiom ctor as =
    [ ctor SentenceAxiom
        { sentenceAxiomParameters = metaParameters
        , sentenceAxiomAttributes = sentenceAxiomAttributes as
        , sentenceAxiomPattern =
            asCommonMetaPattern
                (ImpliesPattern Implies
                    { impliesSort = axiomSort
                    , impliesFirst =
                        App_
                            (sortsDeclaredHead axiomSort)
                            [ liftToMeta
                                (map SortVariableSort objectParameters)
                            ]
                    , impliesSecond = provableLiftedPattern
                    }
                )
        }
    ]
  where
    metaParameters =
        [sv | UnifiedMeta sv <- sentenceAxiomParameters as]
    originalPattern = sentenceAxiomPattern as
    axiomSort =
        case Cofree.tailF (Recursive.project originalPattern) of
            UnifiedObjectPattern _ -> patternMetaSort
            UnifiedMetaPattern p   -> getPatternResultSort undefinedHeadSort p
    objectParameters =
        [sv | UnifiedObject sv <- sentenceAxiomParameters as]
    liftedPattern = liftToMeta originalPattern
    provableLiftedPattern =
        case Cofree.tailF (Recursive.project originalPattern) of
            UnifiedMetaPattern _   -> liftedPattern
            UnifiedObjectPattern _ ->
                App_ (provableHead axiomSort) [liftedPattern]

liftObjectSentence
    :: Sentence Object UnifiedSortVariable CommonKorePattern
    -> [MetaSentence]
liftObjectSentence (SentenceAliasSentence osa) =
    let (mas, axiom) = liftAliasDeclaration osa in
        [ SentenceSymbolSentence mas
        , SentenceAxiomSentence axiom
        ]
liftObjectSentence (SentenceSymbolSentence oss) =
    let (mss, axiom1, axiom2) = liftSymbolDeclaration oss in
        [ SentenceSymbolSentence mss
        , SentenceAxiomSentence axiom1
        , SentenceAxiomSentence axiom2
        ]
liftObjectSentence (SentenceSortSentence ss) =
    let (mss, axiom1, axiom2) = liftSortDeclaration ss in
        [ SentenceSymbolSentence mss
        , SentenceAxiomSentence axiom1
        , SentenceAxiomSentence axiom2
        ]
-- TODO(traiansf): add information that the two lifted definitions
-- below correspond to hooks once this is added to the Semantics-of-K document.
liftObjectSentence (SentenceHookSentence (SentenceHookedSort hss)) =
    liftObjectSentence (SentenceSortSentence hss)
liftObjectSentence (SentenceHookSentence (SentenceHookedSymbol hss)) =
    liftObjectSentence (SentenceSymbolSentence hss)


-- |'liftModule' transforms a 'KoreModule' into a 'MetaModule'
liftModule :: KoreModule -> MetaModule
liftModule m = Module
    { moduleName = moduleName m
    , moduleAttributes = moduleAttributes m
    , moduleSentences = concatMap liftSentence (moduleSentences m)
    }

-- |'liftDefinition' transforms a 'KoreDefinition' into a 'MetaDefinition'
liftDefinition :: KoreDefinition -> MetaDefinition
liftDefinition d = Definition
    { definitionAttributes = definitionAttributes d
    , definitionModules = map liftModule (definitionModules d)
    }
