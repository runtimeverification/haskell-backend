module Test.Kore.Builtin.Bool where

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
import Test.Kore.Builtin.Builtin

prop_or :: Bool -> Bool -> Property
prop_or = propBinary (||) orSymbol

prop_and :: Bool -> Bool -> Property
prop_and = propBinary (&&) andSymbol

prop_xor :: Bool -> Bool -> Property
prop_xor = propBinary xor xorSymbol
  where
    xor u v = (u && not v) || (not u && v)

prop_ne :: Bool -> Bool -> Property
prop_ne = propBinary (/=) neSymbol

prop_eq :: Bool -> Bool -> Property
prop_eq = propBinary (==) eqSymbol

prop_not :: Bool -> Property
prop_not = propUnary not notSymbol

prop_implies :: Bool -> Bool -> Property
prop_implies = propBinary implies impliesSymbol
  where
    implies u v = not u || v

-- | Test a binary operator hooked to the given symbol.
propBinary
    :: (Bool -> Bool -> Bool)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Bool -> Property)
propBinary impl symb =
    \a b ->
        let pat = App_ symb (asPattern <$> [a, b])
        in asPattern (impl a b) === evaluate pat

-- | Test a unary operator hooked to the given symbol
propUnary
    :: (Bool -> Bool)
    -- ^ operator
    -> SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Property)
propUnary impl symb =
    \a ->
        let pat = App_ symb (asPattern <$> [a])
        in asPattern (impl a) === evaluate pat

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
builtinSymbol :: String -> SymbolOrAlias Object
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

{- | Declare a hooked symbol with two arguments.

  The result and arguments all have sort 'boolSort'.

  -}
binarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
binarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol boolSort [boolSort, boolSort]

{- | Declare a hooked symbol with one argument.

  The result and argument have sort 'boolSort'.

 -}
unarySymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
unarySymbolDecl builtinName symbol =
    hookedSymbolDecl builtinName symbol boolSort [boolSort]

boolModuleName :: ModuleName
boolModuleName = ModuleName "BOOL"

{- | Declare the @BOOL@ builtins.
 -}
boolModule :: KoreModule
boolModule =
    Module
        { moduleName = boolModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ boolSortDecl
            , binarySymbolDecl "BOOL.or" orSymbol
            , binarySymbolDecl "BOOL.and" andSymbol
            , binarySymbolDecl "BOOL.xor" xorSymbol
            , binarySymbolDecl "BOOL.ne" neSymbol
            , binarySymbolDecl "BOOL.eq" eqSymbol
            , unarySymbolDecl "BOOL.not" notSymbol
            , binarySymbolDecl "BOOL.implies" impliesSymbol
            ]
        }

evaluate :: CommonPurePattern Object -> CommonPurePattern Object
evaluate pat =
    let (Predicated { term }, _) =
            evalSimplifier (Pattern.simplify tools evaluators pat)
    in term
  where
    tools = extractMetadataTools indexedModule

boolDefinition :: KoreDefinition
boolDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ boolModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = either (error . Kore.Error.printError) id (verify boolDefinition)

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
