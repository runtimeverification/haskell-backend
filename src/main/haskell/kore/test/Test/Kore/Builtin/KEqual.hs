module Test.Kore.Builtin.KEqual
    ( prop_keq
    , prop_kneq
    , test_KEqual
    , test_KIte
    ) where

import Test.QuickCheck
       ( Property, (===) )
import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Control.Lens as Lens
import           Data.Function
                 ( (&) )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )

import           Kore.AST.Builders
                 ( parameterizedSymbol_, sortParameter, symbol_ )
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureSentenceSymbol, groundHead )
import           Kore.AST.PureToKore
                 ( sentencePureToKore )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Error as Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
import qualified Test.Kore.Step.MockSimplifiers as Mock


import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import qualified Test.Kore.Builtin.Builtin as Test.Builtin

prop_kneq :: Bool -> Bool -> Property
prop_kneq = propBinary (/=) kneqSymbol

prop_keq :: Bool -> Bool -> Property
prop_keq = propBinary (==) keqSymbol

-- | Test a binary operator hooked to the given symbol.
propBinary
    :: (Bool -> Bool -> Bool)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Bool -> Property)
propBinary impl symb =
    \a b ->
        let pat = App_ symb (Test.Bool.asPattern <$> [a, b])
        in Test.Bool.asPattern (impl a b) === evaluate pat

keqSymbol :: SymbolOrAlias Object
keqSymbol = Test.Bool.builtinSymbol "keqBool"

kneqSymbol :: SymbolOrAlias Object
kneqSymbol = Test.Bool.builtinSymbol "kneqBool"

kiteSymbol :: SymbolOrAlias Object
kiteSymbol = Test.Bool.builtinSymbol "kiteK"

kEqualModuleName :: ModuleName
kEqualModuleName = ModuleName "KEQUAL"

{- | Declare the @KEQUAL@ builtins.
 -}
kEqualModule :: KoreModule
kEqualModule =
    Module
        { moduleName = kEqualModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ Test.Bool.boolSortDecl
            , Test.Bool.binarySymbolDecl "KEQUAL.eq" keqSymbol
            , Test.Bool.binarySymbolDecl "KEQUAL.neq" kneqSymbol
            , Test.Builtin.hookedSymbolDecl
                "KEQUAL.ite"
                kiteSymbol
                kSort
                [Test.Bool.boolSort, kSort, kSort]
            , sortDecl kSort
            , sortDecl kItemSort
            , sortDecl idSort
            , sentencePureToKore (SentenceSymbolSentence kseqSymbol)
            , sentencePureToKore (SentenceSymbolSentence dotkSymbol)
            , sentencePureToKore (SentenceSymbolSentence injSymbol)
            ]
        }


-- | Declare 'a sort' in a Kore module.
sortDecl :: Sort Object -> KoreSentence
sortDecl sort =
    asSentence (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = sort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
        :: KoreSentenceSort Object)

evaluate :: CommonPurePattern Object -> CommonPurePattern Object
evaluate pat =
    let
        (Predicated { term }, _) =
            evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators pat
                )
    in term

kEqualDefinition :: KoreDefinition
kEqualDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ kEqualModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules =
    either (error . Error.printError) id
        (verify kEqualDefinition)

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup kEqualModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators KEqual.builtinFunctions indexedModule

verify
    :: KoreDefinition
    -> Either (Error.Error VerifyError)
        (Map ModuleName (KoreIndexedModule StepperAttributes))
verify = verifyAndIndexDefinition attrVerify Builtin.koreVerifiers
    where
    attrVerify = defaultAttributesVerification Proxy

test_KEqual :: [TestTree]
test_KEqual =
    [ testCase "equals with variable"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (pat keqSymbol)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (pat keqSymbol)
                )
            )
        )
    , testCase "not equals with variable"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (pat kneqSymbol)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (pat kneqSymbol)
                )
            )
        )
    , testCase "dotk equals dotk"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern True)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ keqSymbol
                        [ App_ dotKHead []
                        , App_ dotKHead []
                        ]
                    )
                )
            )
        )
    , testCase "distinct domain values"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ keqSymbol
                        [ DV_ idSort
                            (BuiltinDomainPattern (StringLiteral_ "t"))
                        , DV_ idSort
                            (BuiltinDomainPattern (StringLiteral_ "x"))
                        ]
                    )
                )
            )
        )
    , testCase "injected distinct domain values"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ keqSymbol
                        [ App_ (injHead idSort kItemSort)
                            [ DV_ idSort
                                (BuiltinDomainPattern (StringLiteral_ "t"))
                            ]
                        , App_ (injHead idSort kItemSort)
                            [ DV_ idSort
                                (BuiltinDomainPattern (StringLiteral_ "x"))
                            ]
                        ]
                    )
                )
            )
        )
    , testCase "distinct Id domain values casted to K"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ keqSymbol
                        [ App_ kSeqHead
                            [ App_ (injHead idSort kItemSort)
                                [ DV_ idSort
                                    (BuiltinDomainPattern (StringLiteral_ "t"))
                                ]
                            , App_ dotKHead []
                            ]
                        , App_ kSeqHead
                            [ App_ (injHead idSort kItemSort)
                                [ DV_ idSort
                                    (BuiltinDomainPattern (StringLiteral_ "x"))
                                ]
                            , App_ dotKHead []
                            ]
                        ]
                    )
                )
            )
        )
    ]
  where
    pat symbol = App_  symbol
        [ Test.Bool.asPattern True
        , Var_ Variable
            { variableName = testId "x"
            , variableSort = Test.Bool.boolSort
            }
        ]

test_KIte :: [TestTree]
test_KIte =
    [ testCase "ite true"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ kiteSymbol
                        [ Test.Bool.asPattern True
                        , Test.Bool.asPattern False
                        , Test.Bool.asPattern True
                        ]
                    )
                )
            )
        )
    , testCase "ite false"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern True)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify
                    tools (Mock.substitutionSimplifier tools) evaluators
                    (App_ kiteSymbol
                        [ Test.Bool.asPattern False
                        , Test.Bool.asPattern False
                        , Test.Bool.asPattern True
                        ]
                    )
                )
            )
        )
    ]

tools :: MetadataTools Object StepperAttributes
tools = extractMetadataTools $ constructorFunctions indexedModule

kseqSymbol :: PureSentenceSymbol Object
kseqSymbol = symbol_ "kseq" AstLocationImplicit [kItemSort, kSort] kSort

dotkSymbol :: PureSentenceSymbol Object
dotkSymbol = symbol_ "dotk" AstLocationImplicit [] kSort

injSymbol :: PureSentenceSymbol Object
injSymbol =
    parameterizedSymbol_ "inj" AstLocationImplicit
        [ from
        , to
        ]
        [ SortVariableSort from ]
        (SortVariableSort to)
  where
    from = sortParameter Proxy "From" AstLocationImplicit
    to = sortParameter Proxy "To" AstLocationImplicit

kSeqHead :: SymbolOrAlias Object
kSeqHead = groundHead "kseq" AstLocationImplicit

dotKHead :: SymbolOrAlias Object
dotKHead = groundHead "dotk" AstLocationImplicit

injHead :: Sort Object -> Sort Object -> SymbolOrAlias Object
injHead fromSort toSort =
    SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = "inj"
        , idLocation = AstLocationImplicit
        }
    , symbolOrAliasParams = [fromSort, toSort]
    }


groundObjectSort :: Text -> Sort Object
groundObjectSort name =
    SortActualSort
        SortActual
        { sortActualName =
            Id
            { getId = name
            , idLocation = AstLocationImplicit
            }
        , sortActualSorts = []
        }

kSort :: Sort Object
kSort = groundObjectSort "SortK"

kItemSort :: Sort Object
kItemSort = groundObjectSort "SortKItem"

idSort :: Sort Object
idSort = groundObjectSort "SortId"

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @kseq@ and @dotk@ are both functional and constructor.
constructorFunctions
    :: KoreIndexedModule StepperAttributes
    -> KoreIndexedModule StepperAttributes
constructorFunctions ixm =
    ixm
        { indexedModuleObjectSymbolSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleObjectSymbolSentences ixm)
        , indexedModuleObjectAliasSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleObjectAliasSentences ixm)
        , indexedModuleImports = recurseIntoImports <$> indexedModuleImports ixm
        }
  where
    constructorFunctions1 ident (atts, defn) =
        ( atts
            & constructor Lens.<>~ Constructor isCons
            & functional Lens.<>~ Functional (isCons || isInj)
            & injective Lens.<>~ Injective (isCons || isInj)
            & sortInjection Lens.<>~ SortInjection isInj
        , defn
        )
      where
        isInj = getId ident == "inj"
        isCons = elem (getId ident) ["kseq", "dotk"]

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)
