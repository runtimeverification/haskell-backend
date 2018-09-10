module Test.Kore.Builtin.KEqual (prop_keq, prop_kneq, test_KEqual) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Test.QuickCheck
       ( Property, (===) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                ( Object )
import           Kore.AST.PureML
                ( CommonPurePattern )
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
                ( StepperAttributes )


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
            ]
        }

evaluate :: CommonPurePattern Object -> CommonPurePattern Object
evaluate pat =
    let
        tools = extractMetadataTools indexedModule
        (ExpandedPattern { term }, _) =
            evalSimplifier (Pattern.simplify tools evaluators pat)
    in term

kEqualDefinition :: KoreDefinition
kEqualDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ kEqualModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
Right indexedModules = verify kEqualDefinition

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
            ( ExpandedPattern.fromPurePattern (pat keqSymbol)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators (pat keqSymbol))
            )
        )
    , testCase "not equals with variable"
        (assertEqual ""
            ( ExpandedPattern.fromPurePattern (pat kneqSymbol)
            , SimplificationProof
            )
            (evalSimplifier
                (Pattern.simplify tools evaluators (pat kneqSymbol))
            )
        )
    ]
  where
    tools = extractMetadataTools indexedModule
    pat symbol = App_  symbol
        [ Test.Bool.asPattern True
        , Var_ Variable
            { variableName = testId "x"
            , variableSort = Test.Bool.boolSort
            }
        ]
