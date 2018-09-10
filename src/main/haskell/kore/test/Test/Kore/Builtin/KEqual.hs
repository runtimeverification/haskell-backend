module Test.Kore.Builtin.KEqual (prop_keq, prop_kneq, test_KEqual) where

import Test.QuickCheck
       ( Property, (===) )
import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.AST.Builders
                 ( parameterizedSymbol_, sortParameter, symbol_ )
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern, PureSentenceSymbol, groundHead )
import           Kore.AST.PureToKore
                 ( sentencePureToKore )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Error as Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )


import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool

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
    case evalSimplifier (Pattern.simplify tools evaluators pat) of
        Left err -> error (Error.printError err)
        Right (ExpandedPattern { term }, _) -> term
  where
    tools = extractMetadataTools indexedModule

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
verify = verifyAndIndexDefinition attrVerify builtinVerifiers
    where
    attrVerify = defaultAttributesVerification Proxy

builtinVerifiers :: Builtin.Verifiers
builtinVerifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = Bool.sortDeclVerifiers
        , symbolVerifiers = Bool.symbolVerifiers
        , patternVerifier = Bool.patternVerifier
        }

test_KEqual :: [TestTree]
test_KEqual =
    [ testCase "equals with variable"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (pat keqSymbol)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators (pat keqSymbol))
            )
        )
    , testCase "not equals with variable"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (pat kneqSymbol)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators (pat kneqSymbol))
            )
        )
    , testCase "distinct Id domain values casted to K"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators
                    (App_ keqSymbol
                        [ App_ kSeqHead
                            [ App_ (injHead idSort kItemSort)
                                [ DV_ idSort
                                    (StringLiteral_ (StringLiteral "t"))
                                ]
                            , App_ dotKHead []
                            ]
                        , App_ kSeqHead
                            [ App_ (injHead idSort kItemSort)
                                [ DV_ idSort
                                    (StringLiteral_ (StringLiteral "x"))
                                ]
                            , App_ dotKHead []
                            ]
                        ]
                    )
                )
            )
        )
    , testCase "injected distinct domain values"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators
                    (App_ keqSymbol
                        [ App_ (injHead idSort kItemSort)
                            [ DV_ idSort
                                (StringLiteral_ (StringLiteral "t"))
                            ]
                        , App_ (injHead idSort kItemSort)
                            [ DV_ idSort
                                (StringLiteral_ (StringLiteral "x"))
                            ]
                        ]
                    )
                )
            )
        )
    , testCase "distinct domain values"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern False)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators
                    (App_ keqSymbol
                        [ DV_ idSort
                            (StringLiteral_ (StringLiteral "t"))
                        , DV_ idSort
                            (StringLiteral_ (StringLiteral "x"))
                        ]
                    )
                )
            )
        )
    , testCase "dotk equals dotk"
        (assertEqual ""
            (Right
                ( ExpandedPattern.fromPurePattern (Test.Bool.asPattern True)
                , SimplificationProof
                )
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators
                    (App_ keqSymbol
                        [ App_ dotKHead []
                        , App_ dotKHead []
                        ]
                    )
                )
            )
        )
    ]
  where
    tools = constructorFunctions (extractMetadataTools indexedModule)
    pat symbol = App_  symbol
        [ Test.Bool.asPattern True
        , Var_ Variable
            { variableName = testId "x"
            , variableSort = Test.Bool.boolSort
            }
        ]

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


groundObjectSort :: String -> Sort Object
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
constructorFunctions :: MetadataTools Object StepperAttributes -> MetadataTools Object StepperAttributes
constructorFunctions tools =
    tools
    { symAttributes = \h -> let atts = symAttributes tools h in
        atts
        { isConstructor = isConstructor atts || isFunction atts || isCons h
        , isFunctional = isFunctional atts || isCons h || isInj h
        , isInjective =
            isInjective atts || isFunction atts || isCons h || isInj h
        , isSortInjection = isSortInjection atts || isInj h
        }
    }
  where
    isInj :: SymbolOrAlias Object -> Bool
    isInj h =
        getId (symbolOrAliasConstructor h) == "inj"
    isCons :: SymbolOrAlias Object -> Bool
    isCons h = getId (symbolOrAliasConstructor h) `elem` ["kseq", "dotk"]

