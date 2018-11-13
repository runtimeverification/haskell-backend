{-# LANGUAGE MagicHash #-}

module Test.Kore.Builtin.Int where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import qualified Control.Monad.Trans as Trans
import           Data.Bits
                 ( complement, shift, xor, (.&.), (.|.) )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Attribute.Smtlib
                 ( smtlibAttribute )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
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
import           Test.Kore.Builtin.Bool
                 ( boolSort )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genIntegerPattern :: Gen (CommonPurePattern Object)
genIntegerPattern = asPattern <$> genInteger

genConcreteIntegerPattern :: Gen (ConcretePurePattern Object)
genConcreteIntegerPattern = asConcretePattern <$> genInteger

-- | Test a unary operator hooked to the given symbol
testUnary
    :: TestName
    -> (Integer -> Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testUnary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a])
        (===) (asExpandedPattern $ impl a) =<< Trans.lift (evaluate pat)

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: TestName
    -> (Integer -> Integer -> Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testBinary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        b <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a, b])
        (===) (asExpandedPattern $ impl a b) =<< Trans.lift (evaluate pat)

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: TestName
    -> (Integer -> Integer -> Bool)
    -- ^ implementation
    -> SymbolOrAlias Object
    -- ^ symbol
    -> TestTree
testComparison name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        b <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a, b])
        (===) (Test.Bool.asExpandedPattern $ impl a b)
            =<< Trans.lift (evaluate pat)

-- | Test a partial unary operator hooked to the given symbol.
testPartialUnary
    :: TestName
    -> (Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testPartialUnary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a])
        (===) (asPartialExpandedPattern $ impl a) =<< Trans.lift (evaluate pat)

-- | Test a partial binary operator hooked to the given symbol.
testPartialBinary
    :: TestName
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testPartialBinary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        b <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a, b])
        (===) (asPartialExpandedPattern $ impl a b)
            =<< Trans.lift (evaluate pat)

-- | Test a partial binary operator hooked to the given symbol, passing zero as
-- the second argument.
testPartialBinaryZero
    :: TestName
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testPartialBinaryZero name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a, 0])
        (===) (asPartialExpandedPattern $ impl a 0)
            =<< Trans.lift (evaluate pat)

-- | Test a partial ternary operator hooked to the given symbol.
testPartialTernary
    :: TestName
    -> (Integer -> Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> TestTree
testPartialTernary name impl symb =
    testPropertyWithSolver name property
  where
    property = do
        a <- forAll genInteger
        b <- forAll genInteger
        c <- forAll genInteger
        let pat = App_ symb (asPattern <$> [a, b, c])
        (===) (asPartialExpandedPattern $ impl a b c)
            =<< Trans.lift (evaluate pat)

-- Comparison operators
test_gt :: TestTree
test_gt = testComparison "INT.gt" (>) gtSymbol

test_ge :: TestTree
test_ge = testComparison "INT.ge" (>=) geSymbol

test_eq :: TestTree
test_eq = testComparison "INT.eq" (==) eqSymbol

test_le :: TestTree
test_le = testComparison "INT.le" (<=) leSymbol

test_lt :: TestTree
test_lt = testComparison "INT.lt" (<) ltSymbol

test_ne :: TestTree
test_ne = testComparison "INT.ne" (/=) neSymbol

gtSymbol :: SymbolOrAlias Object
gtSymbol = builtinSymbol "gtInt"

geSymbol :: SymbolOrAlias Object
geSymbol = builtinSymbol "geInt"

eqSymbol :: SymbolOrAlias Object
eqSymbol = builtinSymbol "eqInt"

leSymbol :: SymbolOrAlias Object
leSymbol = builtinSymbol "leInt"

ltSymbol :: SymbolOrAlias Object
ltSymbol = builtinSymbol "ltInt"

neSymbol :: SymbolOrAlias Object
neSymbol = builtinSymbol "neInt"

-- Ordering operations
test_min :: TestTree
test_min = testBinary "INT.min" min minSymbol

test_max :: TestTree
test_max = testBinary "INT.max" max maxSymbol

minSymbol :: SymbolOrAlias Object
minSymbol = builtinSymbol "minInt"

maxSymbol :: SymbolOrAlias Object
maxSymbol = builtinSymbol "maxInt"

-- Arithmetic operations
test_add :: TestTree
test_add = testBinary "INT.add" (+) addSymbol

test_sub :: TestTree
test_sub = testBinary "INT.sub" (-) subSymbol

test_mul :: TestTree
test_mul = testBinary "INT.mul" (*) mulSymbol

test_abs :: TestTree
test_abs = testUnary "INT.abs" abs absSymbol

addSymbol :: SymbolOrAlias Object
addSymbol = builtinSymbol "addInt"

subSymbol :: SymbolOrAlias Object
subSymbol = builtinSymbol "subInt"

mulSymbol :: SymbolOrAlias Object
mulSymbol = builtinSymbol "mulInt"

absSymbol :: SymbolOrAlias Object
absSymbol = builtinSymbol "absInt"

-- Division
test_tdiv :: TestTree
test_tdiv = testPartialBinary "INT.tdiv" tdiv tdivSymbol

tdiv :: Integer -> Integer -> Maybe Integer
tdiv n d
  | d == 0 = Nothing
  | otherwise = Just (quot n d)

test_tmod :: TestTree
test_tmod = testPartialBinary "INT.tmod" tmod tmodSymbol

tmod :: Integer -> Integer -> Maybe Integer
tmod n d
  | d == 0 = Nothing
  | otherwise = Just (rem n d)

tdivSymbol :: SymbolOrAlias Object
tdivSymbol = builtinSymbol "tdivInt"

tmodSymbol :: SymbolOrAlias Object
tmodSymbol = builtinSymbol "tmodInt"

test_tdivZero :: TestTree
test_tdivZero = testPartialBinaryZero "INT.tdiv by 0" tdiv tdivSymbol

test_tmodZero :: TestTree
test_tmodZero = testPartialBinaryZero "INT.tmod by 0" tmod tmodSymbol

-- Bitwise operations
test_and :: TestTree
test_and = testBinary "INT.and" (.&.) andSymbol

test_or :: TestTree
test_or = testBinary "INT.or" (.|.) orSymbol

test_xor :: TestTree
test_xor = testBinary "INT.xor" xor xorSymbol

test_not :: TestTree
test_not = testUnary "INT.not" complement notSymbol

test_shl :: TestTree
test_shl = testBinary "INT.shl" shl shlSymbol
  where shl a = shift a . fromInteger

test_shr :: TestTree
test_shr = testBinary "INT.shr" shr shrSymbol
  where shr a = shift a . fromInteger . negate

andSymbol, orSymbol, xorSymbol, notSymbol, shlSymbol, shrSymbol
    :: SymbolOrAlias Object
andSymbol = builtinSymbol "andInt"
orSymbol = builtinSymbol "orInt"
xorSymbol = builtinSymbol "xorInt"
notSymbol = builtinSymbol "notInt"
shlSymbol = builtinSymbol "shlInt"
shrSymbol = builtinSymbol "shrInt"

-- Exponential and logarithmic operations
pow :: Integer -> Integer -> Maybe Integer
pow b e
    | e < 0 = Nothing
    | otherwise = Just (b ^ e)

test_pow :: TestTree
test_pow = testPartialBinary "INT.pow" pow powSymbol

powmod :: Integer -> Integer -> Integer -> Maybe Integer
powmod b e m
    | m == 0 = Nothing
    | e < 0 && recipModInteger b m == 0 = Nothing
    | otherwise = Just (powModInteger b e m)

test_powmod :: TestTree
test_powmod = testPartialTernary "INT.powmod" powmod powmodSymbol

log2 :: Integer -> Maybe Integer
log2 n
    | n > 0 = Just (smallInteger (integerLog2# n))
    | otherwise = Nothing

test_log2 :: TestTree
test_log2 = testPartialUnary "INT.log2" log2 log2Symbol

powSymbol :: SymbolOrAlias Object
powSymbol = builtinSymbol "powInt"

powmodSymbol :: SymbolOrAlias Object
powmodSymbol = builtinSymbol "powmodInt"

log2Symbol :: SymbolOrAlias Object
log2Symbol = builtinSymbol "log2Int"

emodSymbol :: SymbolOrAlias Object
emodSymbol = builtinSymbol "emodInt"

test_emod :: [TestTree]
test_emod =
    [ testInt
        "emod normal"
        emodSymbol
        (asPattern <$> [193, 12])
        (asExpandedPattern 1)
    , testInt
        "emod negative lhs"
        emodSymbol
        (asPattern <$> [-193, 12])
        (asExpandedPattern 11)
    , testInt
        "emod negative rhs"
        emodSymbol
        (asPattern <$> [193, -12])
        (asExpandedPattern 1)
    , testInt
        "emod both negative"
        emodSymbol
        (asPattern <$> [-193, -12])
        (asExpandedPattern (-1))
    , testInt
        "emod bottom"
        emodSymbol
        (asPattern <$> [193, 0])
        bottom
    ]

-- | Another name for asPattern.
intLiteral :: Integer -> CommonPurePattern Object
intLiteral = asPattern

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: Integer -> CommonPurePattern Object
asPattern = Int.asPattern intSort

-- | Specialize 'Int.asConcretePattern' to the builtin sort 'intSort'.
asConcretePattern :: Integer -> ConcretePurePattern Object
asConcretePattern = Int.asConcretePattern intSort

-- | Specialize 'Int.asExpandedPattern' to the builtin sort 'intSort'.
asExpandedPattern :: Integer -> CommonExpandedPattern Object
asExpandedPattern = Int.asExpandedPattern intSort

-- | Specialize 'Int.asPartialPattern' to the builtin sort 'intSort'.
asPartialExpandedPattern :: Maybe Integer -> CommonExpandedPattern Object
asPartialExpandedPattern = Int.asPartialExpandedPattern intSort

-- | A sort to hook to the builtin @INT.Int@.
intSort :: Sort Object
intSort =
    SortActualSort SortActual
        { sortActualName = testId "Int"
        , sortActualSorts = []
        }

-- | Declare 'intSort' in a Kore module.
intSortDecl :: KoreSentence
intSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = intSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "INT.Int" ]
        }
        :: KoreSentenceSort Object)

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

importBool :: KoreSentence
importBool =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Bool.boolModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

intModuleName :: ModuleName
intModuleName = ModuleName "INT"

comparisonSymbolDecl
    :: SymbolOrAlias Object -> [CommonKorePattern] -> KoreSentence
comparisonSymbolDecl symbol =
    hookedSymbolDecl symbol boolSort [intSort, intSort]

unarySymbolDecl
   :: SymbolOrAlias Object -> [CommonKorePattern] -> KoreSentence
unarySymbolDecl symbol =
    hookedSymbolDecl symbol intSort [intSort]

binarySymbolDecl
    :: SymbolOrAlias Object -> [CommonKorePattern] -> KoreSentence
binarySymbolDecl symbol =
    hookedSymbolDecl symbol intSort [intSort, intSort]

{- | Declare the @INT@ builtins.
 -}
intModule :: KoreModule
intModule =
    Module
        { moduleName = intModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importBool
            , intSortDecl
            -- comparison symbols
            , comparisonSymbolDecl gtSymbol
                [hookAttribute "INT.gt", smtlibAttribute ">"]
            , comparisonSymbolDecl geSymbol
                [hookAttribute "INT.ge", smtlibAttribute ">="]
            , comparisonSymbolDecl eqSymbol
                [hookAttribute "INT.eq", smtlibAttribute "="]
            , comparisonSymbolDecl leSymbol
                [hookAttribute "INT.le", smtlibAttribute "<="]
            , comparisonSymbolDecl ltSymbol
                [hookAttribute "INT.lt", smtlibAttribute "<"]
            , comparisonSymbolDecl neSymbol
                [hookAttribute "INT.ne", smtlibAttribute "distinct"]

            , binarySymbolDecl minSymbol
                [hookAttribute "INT.min", smtlibAttribute "int_min"]
            , binarySymbolDecl maxSymbol
                [hookAttribute "INT.max", smtlibAttribute "int_max"]
            , binarySymbolDecl addSymbol
                [hookAttribute "INT.add", smtlibAttribute "+"]
            , binarySymbolDecl subSymbol
                [hookAttribute "INT.sub", smtlibAttribute "-"]
            , binarySymbolDecl mulSymbol
                [hookAttribute "INT.mul", smtlibAttribute "*"]
            , unarySymbolDecl absSymbol
                [hookAttribute "INT.abs", smtlibAttribute "int_abs"]
            , binarySymbolDecl tdivSymbol
                [hookAttribute "INT.tdiv", smtlibAttribute "div"]
            , binarySymbolDecl tmodSymbol
                [hookAttribute "INT.tmod", smtlibAttribute "mod"]
            , binarySymbolDecl emodSymbol
                [hookAttribute "INT.emod", smtlibAttribute "mod"]
            , binarySymbolDecl andSymbol
                [hookAttribute "INT.and"]
            , binarySymbolDecl orSymbol
                [hookAttribute "INT.or"]
            , binarySymbolDecl xorSymbol
                [hookAttribute "INT.xor"]
            , unarySymbolDecl notSymbol
                [hookAttribute "INT.not"]
            , binarySymbolDecl shlSymbol
                [hookAttribute "INT.shl"]
            , binarySymbolDecl shrSymbol
                [hookAttribute "INT.shr"]
            , binarySymbolDecl powSymbol
                [hookAttribute "INT.pow"]
            , hookedSymbolDecl powmodSymbol intSort [intSort, intSort, intSort]
                [hookAttribute "INT.powmod"]
            , unarySymbolDecl log2Symbol
                [hookAttribute "INT.log2"]
            ]
        }

evaluate
    :: CommonPurePattern Object
    -> SMT (CommonExpandedPattern Object)
evaluate pat = do
    (expanded, _) <-
        evalSimplifier
        $ Pattern.simplify
            testTools
            testSubstitutionSimplifier
            evaluators
            pat
    return expanded

testTools :: MetadataTools Object StepperAttributes
testTools = extractMetadataTools indexedModule

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object Simplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testTools

intDefinition :: KoreDefinition
intDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ Test.Bool.boolModule, intModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify intDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup intModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators Int.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

testInt
    :: String
    -> SymbolOrAlias Object
    -> [CommonPurePattern Object]
    -> CommonExpandedPattern Object
    -> TestTree
testInt = testSymbol evaluate
