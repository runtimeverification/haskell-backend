{-# LANGUAGE MagicHash #-}

module Test.Kore.Builtin.Int where

import Test.QuickCheck
       ( Property, (===) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( hookAttribute )
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
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin

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

propComparison
    :: (Integer -> Integer -> Bool)
    -- ^ implementation
    -> SymbolOrAlias Object
    -- ^ symbol
    -> (Integer -> Integer -> Property)
propComparison impl symb a b =
    let pat = App_ symb (asPattern <$> [a, b])
    in Test.Bool.asExpandedPattern (impl a b) === evaluate pat

prop_min :: Integer -> Integer -> Property
prop_min = propBinary min minSymbol

prop_max :: Integer -> Integer -> Property
prop_max = propBinary max maxSymbol

prop_add :: Integer -> Integer -> Property
prop_add = propBinary (+) addSymbol

prop_sub :: Integer -> Integer -> Property
prop_sub = propBinary (-) subSymbol

prop_mul :: Integer -> Integer -> Property
prop_mul = propBinary (*) mulSymbol

minSymbol :: SymbolOrAlias Object
minSymbol = builtinSymbol "minInt"

maxSymbol :: SymbolOrAlias Object
maxSymbol = builtinSymbol "maxInt"

addSymbol :: SymbolOrAlias Object
addSymbol = builtinSymbol "addInt"

subSymbol :: SymbolOrAlias Object
subSymbol = builtinSymbol "subInt"

mulSymbol :: SymbolOrAlias Object
mulSymbol = builtinSymbol "mulInt"

intLiteral :: Integer -> CommonPurePattern Object
intLiteral n = DV_ intSort (BuiltinDomainPattern $ StringLiteral_ $ show n)


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

prop_abs :: Integer -> Property
prop_abs = propUnary abs absSymbol

absSymbol :: SymbolOrAlias Object
absSymbol = builtinSymbol "absInt"

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

prop_tdivZero :: Integer -> Property
prop_tdivZero = propPartialBinaryZero tdiv tdivSymbol

prop_tmodZero :: Integer -> Property
prop_tmodZero = propPartialBinaryZero tmod tmodSymbol

-- | Test a partial binary operator hooked to the given symbol, passing zero as
-- the second argument.
propPartialBinaryZero
    :: (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Property)
propPartialBinaryZero impl symb a =
    let pat = App_ symb (asPattern <$> [a, 0])
    in asPartialExpandedPattern (impl a 0) === evaluate pat

pow :: Integer -> Integer -> Maybe Integer
pow b e
    | e < 0 = Nothing
    | otherwise = Just (b ^ e)

prop_pow :: Integer -> Integer -> Property
prop_pow = propPartialBinary pow powSymbol

powSymbol :: SymbolOrAlias Object
powSymbol = builtinSymbol "powInt"

powmod :: Integer -> Integer -> Integer -> Maybe Integer
powmod b e m
    | m == 0 = Nothing
    | e < 0 && recipModInteger b m == 0 = Nothing
    | otherwise = Just (powModInteger b e m)

prop_powmod :: Integer -> Integer -> Integer -> Property
prop_powmod = propPartialTernary powmod powmodSymbol

powmodSymbol :: SymbolOrAlias Object
powmodSymbol = builtinSymbol "powmodInt"

log2 :: Integer -> Maybe Integer
log2 n
    | n > 0 = Just (smallInteger (integerLog2# n))
    | otherwise = Nothing

prop_log2 :: Integer -> Property
prop_log2 = propPartialUnary log2 log2Symbol

log2Symbol :: SymbolOrAlias Object
log2Symbol = builtinSymbol "log2Int"

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

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: Integer -> CommonPurePattern Object
asPattern = Int.asPattern intSort

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
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
builtinSymbol :: String -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

{- | Declare a hooked symbol with one argument.

  The result and argument have sort 'intSort'.

 -}
unarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
unarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol intSort [intSort]

{- | Declare a hooked symbol with two arguments.

  The result and arguments all have sort 'intSort'.

  -}
binarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
binarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol intSort [intSort, intSort]

{- | Declare a hooked symbol with three arguments.

  The result and arguments all have sort 'intSort'.

  -}
ternarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
ternarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol intSort [intSort, intSort, intSort]

{- | Declare a hooked symbol with two arguments.

  The arguments have sort 'intSort' and the result is 'Test.Bool.boolSort'.

  -}
comparisonSymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
comparisonSymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol Test.Bool.boolSort [intSort, intSort]

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
            , comparisonSymbolDecl "INT.gt" gtSymbol
            , comparisonSymbolDecl "INT.ge" geSymbol
            , comparisonSymbolDecl "INT.eq" eqSymbol
            , comparisonSymbolDecl "INT.le" leSymbol
            , comparisonSymbolDecl "INT.lt" ltSymbol
            , comparisonSymbolDecl "INT.ne" neSymbol
            , binarySymbolDecl "INT.min" minSymbol
            , binarySymbolDecl "INT.max" maxSymbol
            , binarySymbolDecl "INT.add" addSymbol
            , binarySymbolDecl "INT.sub" subSymbol
            , binarySymbolDecl "INT.mul" mulSymbol
            , unarySymbolDecl "INT.abs" absSymbol
            , binarySymbolDecl "INT.tdiv" tdivSymbol
            , binarySymbolDecl "INT.tmod" tmodSymbol
            , binarySymbolDecl "INT.pow" powSymbol
            , ternarySymbolDecl "INT.powmod" powmodSymbol
            , unarySymbolDecl "INT.log2" log2Symbol
            ]
        }

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier $ Pattern.simplify tools evaluators pat
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
