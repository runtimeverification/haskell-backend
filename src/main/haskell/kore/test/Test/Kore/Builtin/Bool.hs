module Test.Kore.Builtin.Bool where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import           Test.Tasty

import qualified Control.Monad.Trans as Trans
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Smtlib
                 ( smtlibAttribute )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           SMT
                 ( SMT )

import           Test.Kore
                 ( testId )
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

test_or :: TestTree
test_or = testBinary "BOOL.or" (||) orSymbol

test_and :: TestTree
test_and = testBinary "BOOL.and" (&&) andSymbol

test_xor :: TestTree
test_xor = testBinary "BOOL.xor" xor xorSymbol
  where
    xor u v = (u && not v) || (not u && v)

test_ne :: TestTree
test_ne = testBinary "BOOL.ne" (/=) neSymbol

test_eq :: TestTree
test_eq = testBinary "BOOL.eq" (==) eqSymbol

test_not :: TestTree
test_not = testUnary "BOOL.not" not notSymbol

test_implies :: TestTree
test_implies = testBinary "BOOL.implies" implies impliesSymbol
  where
    implies u v = not u || v

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: TestName
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testBinary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let pat = App_ symb (asPattern <$> [a, b])
        (===) (asPattern $ impl a b) =<< evaluate pat

-- | Test a unary operator hooked to the given symbol
testUnary
    :: TestName
    -> (Bool -> Bool)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testUnary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll Gen.bool
        let pat = App_ symb (asPattern <$> [a])
        (===) (asPattern $ impl a) =<< evaluate pat

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: Bool -> CommonPurePattern Object
asPattern = Bool.asPattern boolSort

-- | Specialize 'Bool.asExpandedPattern' to the builtin sort 'boolSort'.
asExpandedPattern :: Bool -> CommonExpandedPattern Object
asExpandedPattern = Bool.asExpandedPattern boolSort

-- | A sort to hook to the builtin @BOOL.Bool@.
boolSort :: Sort Object
boolSort =
    SortActualSort SortActual
        { sortActualName = testId "Bool"
        , sortActualSorts = []
        }

-- | Declare 'boolSort' in a Kore module.
boolSortDecl :: KoreSentence
boolSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = boolSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "BOOL.Bool" ]
        }
        :: KoreSentenceSort Object)

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

orSymbol :: SymbolOrAlias Object
orSymbol = builtinSymbol "orBool"

andSymbol :: SymbolOrAlias Object
andSymbol = builtinSymbol "andBool"

xorSymbol :: SymbolOrAlias Object
xorSymbol = builtinSymbol "xorBool"

neSymbol :: SymbolOrAlias Object
neSymbol = builtinSymbol "neBool"

eqSymbol :: SymbolOrAlias Object
eqSymbol = builtinSymbol "eqBool"

notSymbol :: SymbolOrAlias Object
notSymbol = builtinSymbol "notBool"

impliesSymbol :: SymbolOrAlias Object
impliesSymbol = builtinSymbol "impliesBool"

boolModuleName :: ModuleName
boolModuleName = ModuleName "BOOL"

binarySymbolDecl :: SymbolOrAlias Object -> [CommonKorePattern] -> KoreSentence
binarySymbolDecl symbol attrs =
    hookedSymbolDecl symbol boolSort [boolSort, boolSort] attrs

{- | Declare the @BOOL@ builtins.
 -}
boolModule :: KoreModule
boolModule =
    Module
        { moduleName = boolModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ boolSortDecl
            , binarySymbolDecl orSymbol
                [hookAttribute "BOOL.or", smtlibAttribute "or"]
            , binarySymbolDecl andSymbol
                [hookAttribute "BOOL.and", smtlibAttribute "and"]
            , binarySymbolDecl xorSymbol
                [hookAttribute "BOOL.xor", smtlibAttribute "xor"]
            , binarySymbolDecl neSymbol
                [hookAttribute "BOOL.ne", smtlibAttribute "distinct"]
            , binarySymbolDecl eqSymbol
                [hookAttribute "BOOL.eq", smtlibAttribute "="]
            , binarySymbolDecl impliesSymbol
                [hookAttribute "BOOL.implies", smtlibAttribute "=>"]
            , hookedSymbolDecl notSymbol boolSort [boolSort]
                [hookAttribute "BOOL.not", smtlibAttribute "not"]
            ]
        }

evaluate
    :: CommonPurePattern Object
    -> PropertyT SMT (CommonPurePattern Object)
evaluate pat = do
    (Predicated { term }, _) <-
        Trans.lift
        $ evalSimplifier
        $ Pattern.simplify
            testTools
            testSubstitutionSimplifier
            evaluators
            pat
    return term

testTools :: MetadataTools Object StepperAttributes
testTools = extractMetadataTools indexedModule

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object Simplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testTools

boolDefinition :: KoreDefinition
boolDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ boolModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules =
    either (error . Kore.Error.printError) id (verify boolDefinition)

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup boolModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators Bool.builtinFunctions indexedModule

verify
    :: KoreDefinition
    -> Either (Kore.Error.Error VerifyError)
        (Map ModuleName (KoreIndexedModule StepperAttributes))
verify = verifyAndIndexDefinition attrVerify Builtin.koreVerifiers
  where
    attrVerify = defaultAttributesVerification Proxy
