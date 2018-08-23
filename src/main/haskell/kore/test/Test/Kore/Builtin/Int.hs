module Test.Kore.Builtin.Int where

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
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import           Kore.Builtin.Hook
                 ( hookAttribute )
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import Test.Kore
       ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin

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
propComparison impl symb =
    \a b ->
        let pat = App_ symb (asPattern <$> [a, b])
        in Test.Bool.asPattern (impl a b) === evaluate pat

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: Integer -> CommonPurePattern Object
asPattern = Int.asPattern intSort

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

{- | Declare a hooked symbol with two arguments.

  The result and arguments all have sort 'intSort'.

  -}
binarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
binarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol intSort [intSort, intSort]

{- | Declare a hooked symbol with one argument.

  The result and argument have sort 'intSort'.

 -}
unarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
unarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol intSort [intSort]

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
            ]
        }

evaluate :: CommonPurePattern Object -> CommonPurePattern Object
evaluate pat =
    case evalSimplifier (Pattern.simplify tools builtinFunctions pat) of
        Left err -> error (Kore.Error.printError err)
        Right (ExpandedPattern { term }, _) -> term
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

builtinFunctions :: Map (Id Object) [Builtin.Function]
builtinFunctions = Builtin.functionContext Int.builtinFunctions indexedModule

verify
    :: KoreDefinition
    -> Map ModuleName (KoreIndexedModule StepperAttributes)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify builtinVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

builtinVerifiers :: Builtin.Verifiers
builtinVerifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = Int.sortDeclVerifiers
        , symbolVerifiers = Int.symbolVerifiers
        , patternVerifier = Int.patternVerifier
        }
