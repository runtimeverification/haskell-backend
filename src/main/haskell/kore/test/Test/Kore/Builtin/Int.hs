{-# LANGUAGE MagicHash #-}

module Test.Kore.Builtin.Int where

import Test.QuickCheck
       ( Property, (===) )
import Test.Tasty
       ( TestTree )

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

import           Test.Kore
                 ( testId )
import           Test.Kore.Builtin.Bool
                 ( boolSort )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Step.MockSimplifiers as Mock

-- | Test a unary operator hooked to the given symbol
propUnary
    :: (Integer -> Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Property)
propUnary impl symb a =
    let pat = App_ symb (asPattern <$> [a])
    in asExpandedPattern (impl a) === evaluate pat

-- | Test a binary operator hooked to the given symbol.
propBinary
    :: (Integer -> Integer -> Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Property)
propBinary impl symb a b =
    let pat = App_ symb (asPattern <$> [a, b])
    in asExpandedPattern (impl a b) === evaluate pat

-- | Test a comparison operator hooked to the given symbol
propComparison
    :: (Integer -> Integer -> Bool)
    -- ^ implementation
    -> SymbolOrAlias Object
    -- ^ symbol
    -> (Integer -> Integer -> Property)
propComparison impl symb a b =
    let pat = App_ symb (asPattern <$> [a, b])
    in Test.Bool.asExpandedPattern (impl a b) === evaluate pat

-- | Test a partial unary operator hooked to the given symbol.
propPartialUnary
    :: (Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Property)
propPartialUnary impl symb a =
    let pat = App_ symb (asPattern <$> [a])
    in asPartialExpandedPattern (impl a) === evaluate pat

-- | Test a partial binary operator hooked to the given symbol.
propPartialBinary
    :: (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Property)
propPartialBinary impl symb a b =
    let pat = App_ symb (asPattern <$> [a, b])
    in asPartialExpandedPattern (impl a b) === evaluate pat

-- | Test a partial binary operator hooked to the given symbol, passing zero as
-- the second argument.
propPartialBinaryZero
    :: (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Property)
propPartialBinaryZero impl symb a = propPartialBinary impl symb a 0

-- | Test a partial ternary operator hooked to the given symbol.
propPartialTernary
    :: (Integer -> Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Integer -> Property)
propPartialTernary impl symb a b c =
    let pat = App_ symb (asPattern <$> [a, b, c])
    in asPartialExpandedPattern (impl a b c) === evaluate pat

-- Comparison operators
prop_gt :: Integer -> Integer -> Property
prop_gt = propComparison (>) gtSymbol

prop_ge :: Integer -> Integer -> Property
prop_ge = propComparison (>=) geSymbol

prop_eq :: Integer -> Integer -> Property
prop_eq = propComparison (==) eqSymbol

prop_le :: Integer -> Integer -> Property
prop_le = propComparison (<=) leSymbol

prop_lt :: Integer -> Integer -> Property
prop_lt = propComparison (<) ltSymbol

prop_ne :: Integer -> Integer -> Property
prop_ne = propComparison (/=) neSymbol

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
prop_min :: Integer -> Integer -> Property
prop_min = propBinary min minSymbol

prop_max :: Integer -> Integer -> Property
prop_max = propBinary max maxSymbol

minSymbol :: SymbolOrAlias Object
minSymbol = builtinSymbol "minInt"

maxSymbol :: SymbolOrAlias Object
maxSymbol = builtinSymbol "maxInt"

-- Arithmetic operations
prop_add :: Integer -> Integer -> Property
prop_add = propBinary (+) addSymbol

prop_sub :: Integer -> Integer -> Property
prop_sub = propBinary (-) subSymbol

prop_mul :: Integer -> Integer -> Property
prop_mul = propBinary (*) mulSymbol

prop_abs :: Integer -> Property
prop_abs = propUnary abs absSymbol

addSymbol :: SymbolOrAlias Object
addSymbol = builtinSymbol "addInt"

subSymbol :: SymbolOrAlias Object
subSymbol = builtinSymbol "subInt"

mulSymbol :: SymbolOrAlias Object
mulSymbol = builtinSymbol "mulInt"

absSymbol :: SymbolOrAlias Object
absSymbol = builtinSymbol "absInt"

-- Division
prop_tdiv :: Integer -> Integer -> Property
prop_tdiv = propPartialBinary tdiv tdivSymbol

tdiv :: Integer -> Integer -> Maybe Integer
tdiv n d
  | d == 0 = Nothing
  | otherwise = Just (quot n d)

prop_tmod :: Integer -> Integer -> Property
prop_tmod = propPartialBinary tmod tmodSymbol

tmod :: Integer -> Integer -> Maybe Integer
tmod n d
  | d == 0 = Nothing
  | otherwise = Just (rem n d)

tdivSymbol :: SymbolOrAlias Object
tdivSymbol = builtinSymbol "tdivInt"

tmodSymbol :: SymbolOrAlias Object
tmodSymbol = builtinSymbol "tmodInt"

prop_tdivZero :: Integer -> Property
prop_tdivZero = propPartialBinaryZero tdiv tdivSymbol

prop_tmodZero :: Integer -> Property
prop_tmodZero = propPartialBinaryZero tmod tmodSymbol

-- Bitwise operations
prop_and :: Integer -> Integer -> Property
prop_and = propBinary (.&.) andSymbol

prop_or :: Integer -> Integer -> Property
prop_or = propBinary (.|.) orSymbol

prop_xor :: Integer -> Integer -> Property
prop_xor = propBinary xor xorSymbol

prop_not :: Integer -> Property
prop_not = propUnary complement notSymbol

prop_shl :: Integer -> Integer -> Property
prop_shl = propBinary shl shlSymbol
  where shl a = shift a . fromInteger

prop_shr :: Integer -> Integer -> Property
prop_shr = propBinary shr shrSymbol
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

prop_pow :: Integer -> Integer -> Property
prop_pow = propPartialBinary pow powSymbol

powmod :: Integer -> Integer -> Integer -> Maybe Integer
powmod b e m
    | m == 0 = Nothing
    | e < 0 && recipModInteger b m == 0 = Nothing
    | otherwise = Just (powModInteger b e m)

prop_powmod :: Integer -> Integer -> Integer -> Property
prop_powmod = propPartialTernary powmod powmodSymbol

log2 :: Integer -> Maybe Integer
log2 n
    | n > 0 = Just (smallInteger (integerLog2# n))
    | otherwise = Nothing

prop_log2 :: Integer -> Property
prop_log2 = propPartialUnary log2 log2Symbol

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

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier
    $ Pattern.simplify tools (Mock.substitutionSimplifier tools) evaluators pat
  where
    tools = extractMetadataTools indexedModule

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
