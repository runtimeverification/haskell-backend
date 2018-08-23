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

prop_or :: Bool -> Bool -> Property
prop_or a b =
    asPattern (a || b) === evaluate pat
  where
    pat = App_ orSymbol (asPattern <$> [a, b])

prop_and :: Bool -> Bool -> Property
prop_and a b =
    asPattern (a && b) === evaluate pat
  where
    pat = App_ andSymbol (asPattern <$> [a, b])


prop_xor :: Bool -> Bool -> Property
prop_xor a b =
    asPattern (xor a b) === evaluate pat
  where
    pat = App_ xorSymbol (asPattern <$> [a, b])
    xor u v = (u && not v) || (not u && v)

prop_ne :: Bool -> Bool -> Property
prop_ne a b =
    asPattern (a /= b) === evaluate pat
  where
    pat = App_ neSymbol (asPattern <$> [a, b])

prop_not :: Bool -> Property
prop_not a =
    asPattern (not a) === evaluate pat
  where
    pat = App_ notSymbol (asPattern <$> [a])

prop_implies :: Bool -> Bool -> Property
prop_implies a b =
    asPattern (implies a b) === evaluate pat
  where
    pat = App_ impliesSymbol (asPattern <$> [a, b])
    implies u v = not u || v

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: Bool -> CommonPurePattern Object
asPattern = Bool.asPattern boolSort

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

notSymbol :: SymbolOrAlias Object
notSymbol = builtinSymbol "notBool"

impliesSymbol :: SymbolOrAlias Object
impliesSymbol = builtinSymbol "impliesBool"

-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl
    :: String
    -- ^ builtin name
    -> SymbolOrAlias Object
    -- ^ symbol
    -> Sort Object
    -- ^ result sort
    -> [Sort Object]
    -- ^ argument sorts
    -> KoreSentence
hookedSymbolDecl
    builtinName
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
  =
    (asSentence . SentenceHookedSymbol)
        (SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
            :: KoreSentenceSymbol Object
        )
  where
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }
    sentenceSymbolAttributes = Attributes [ hookAttribute builtinName ]

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
            , unarySymbolDecl "BOOL.not" notSymbol
            , binarySymbolDecl "BOOL.implies" impliesSymbol
            ]
        }

evaluate :: CommonPurePattern Object -> CommonPurePattern Object
evaluate pat =
    case evalSimplifier (Pattern.simplify tools builtinFunctions pat) of
        Left err -> error (Kore.Error.printError err)
        Right (ExpandedPattern { term }, _) -> term
  where
    tools = extractMetadataTools indexedModule

boolDefinition :: KoreDefinition
boolDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ boolModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
Right indexedModules = verify boolDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup boolModuleName indexedModules

builtinFunctions :: Map (Id Object) [Builtin.Function]
builtinFunctions = Builtin.functionContext Bool.builtinFunctions indexedModule

verify
    :: KoreDefinition
    -> Either (Kore.Error.Error VerifyError)
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
