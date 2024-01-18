{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Main (
    main,
    displayTestDef,
) where

import Control.Monad (unless, when)
import Control.Monad.Trans.Except (runExcept)
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Char (toLower)
import Data.Int (Int64)
import Data.List (isInfixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text.IO qualified as Text
import GHC.IO.Exception
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property (Property (..))
import Hedgehog.Range qualified as Range
import System.FilePath
import System.Process
import Test.Hspec
import Test.Hspec.Hedgehog

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.LLVM as LLVM
import Booster.LLVM.Internal as Internal
import Booster.Pattern.Base
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Syntax.Json.Internalise (pattern AllowAlias, pattern IgnoreSubsorts)
import Booster.Syntax.Json.Internalise qualified as Syntax
import Booster.Syntax.ParsedKore.Internalise (buildDefinitions, symb)
import Booster.Syntax.ParsedKore.Parser (parseDefinition)
import Kore.Syntax.Json.Types qualified as Syntax
import System.Info (os)

-- A prerequisite for all tests in this suite is that a fixed K
-- definition was compiled in LLVM 'c' mode to produce a dynamic
-- library, and is available under 'test/llvm-kompiled/interpreter.{dylib,so}'

definition, kompiledPath, dlPath :: FilePath
definition = "test/llvm-integration/definition/llvm.k"
kompiledPath = "test/llvm-integration/definition/llvm-kompiled"
dlPath = kompiledPath </> "interpreter" <.> (if os == "darwin" then ".dylib" else ".so")

main :: IO ()
main = hspec llvmSpec

llvmSpec :: Spec
llvmSpec =
    beforeAll_ runKompile $ do
        describe "Load an LLVM simplification library" $ do
            it "fails to load a non-existing library" $
                withDLib "does/not/exist.dl" mkAPI
                    `shouldThrow` \IOError{ioe_description = msg} ->
                        "does/not/exist" `isInfixOf` msg
            it ("loads a valid library from " <> dlPath) $ do
                withDLib dlPath $ \dl -> do
                    api <- mkAPI dl
                    let testString = "testing, one, two, three"
                    s <- api.patt.string.new testString
                    api.patt.dump s `shouldReturn` show testString

        beforeAll loadAPI . modifyMaxSuccess (* 20) $ do
            describe "LLVM boolean simplification" $ do
                it "should leave literal booleans as they are" $
                    propertyTest . boolsRemainProp
                it "should be able to compare numbers" $
                    propertyTest . compareNumbersProp
                it "should simplify boolean terms using `simplify`" $
                    propertyTest . simplifyComparisonProp

            describe "LLVM byte array simplification" $ do
                it "should leave literal byte arrays as they are" $
                    hedgehog . propertyTest . byteArrayProp

            describe "LLVM String handling" $
                it "should work with latin-1strings" $
                    hedgehog . propertyTest . latin1Prop

        beforeAll loadAPI $
            it "should correct sort injections in non KItem maps" $
                hedgehog . propertyTest . mapKItemInjProp

--------------------------------------------------
-- individual hedgehog property tests and helpers

boolsRemainProp
    , compareNumbersProp
    , simplifyComparisonProp ::
        Internal.API -> Property
boolsRemainProp api = property $ do
    b <- forAll Gen.bool
    res <- LLVM.simplifyBool api (boolTerm b)
    res === Right b
compareNumbersProp api = property $ do
    x <- anInt64
    y <- anInt64
    res <- LLVM.simplifyBool api (x `equal` y)
    res === Right (x == y)
simplifyComparisonProp api = property $ do
    x <- anInt64
    y <- anInt64
    res <- LLVM.simplifyTerm api testDef (x `equal` y) boolSort
    res === Right (boolTerm (x == y))

anInt64 :: PropertyT IO Int64
anInt64 = forAll $ Gen.integral (Range.constantBounded :: Range Int64)

byteArrayProp :: Internal.API -> Property
byteArrayProp api = property $ do
    i <- forAll $ Gen.int (Range.linear 0 1024)
    let ba = BS.pack $ take i $ cycle ['\255', '\254' .. '\0']
    res <- LLVM.simplifyTerm api testDef (bytesTerm ba) bytesSort
    res === Right (bytesTerm ba)
    ba' <- forAll $ Gen.bytes $ Range.linear 0 1024
    res' <- LLVM.simplifyTerm api testDef (bytesTerm ba') bytesSort
    res' === Right (bytesTerm ba')

-- Round-trip test passing syntactic strings through the simplifier
-- and back. latin-1 characters should be left as they are (treated as
-- bytes internally). UTF-8 code points beyond latin-1 are forbidden.
latin1Prop :: Internal.API -> Property
latin1Prop api = property $ do
    txt <- forAll $ Gen.text (Range.linear 0 123) Gen.latin1
    let stringDV = fromSyntacticString txt
    simplified <- LLVM.simplifyTerm api testDef stringDV stringSort
    Right stringDV === simplified
    Right txt === (toSyntacticString <$> simplified)
  where
    fromSyntacticString :: Text -> Term
    fromSyntacticString =
        either (error . show) id
            . runExcept
            . Syntax.internaliseTerm AllowAlias IgnoreSubsorts Nothing testDef
            . Syntax.KJDV syntaxStringSort
    syntaxStringSort :: Syntax.Sort
    syntaxStringSort = Syntax.SortApp (Syntax.Id "SortString") []
    toSyntacticString :: Term -> Text
    toSyntacticString t =
        case externaliseTerm t of
            Syntax.KJDV s txt
                | s == syntaxStringSort -> txt
                | otherwise -> error $ "Unexpected sort " <> show s
            otherTerm -> error $ "Unexpected term " <> show otherTerm

mapKItemInjProp :: Internal.API -> Property
mapKItemInjProp api = property $ do
    let k = wrapIntTerm 1
    let v = wrapIntTerm 2
    res <- LLVM.simplifyTerm api testDef (update k v) (SortApp "SortMapValToVal" [])
    res === Right (singleton k v)
  where
    update k v =
        SymbolApplication
            (defSymbols Map.! "LblMapValToVal'Coln'primitiveUpdate")
            []
            [ SymbolApplication
                (defSymbols Map.! "Lbl'Stop'MapValToVal")
                []
                []
            , k
            , v
            ]

    singleton k v =
        SymbolApplication
            (defSymbols Map.! "Lbl'Unds'Val2Val'Pipe'-'-GT-Unds'")
            []
            [k, v]

    wrapIntTerm :: Int -> Term
    wrapIntTerm i =
        SymbolApplication
            (defSymbols Map.! "inj")
            [SortApp "SortWrappedInt" [], SortApp "SortVal" []]
            [ SymbolApplication
                (defSymbols Map.! "LblwrapInt")
                []
                [intTerm i]
            ]

------------------------------------------------------------

runKompile :: IO ()
runKompile = do
    putStrLn "[Info] Compiling definition to produce a dynamic LLVM library.."
    callProcess
        "kompile"
        [ definition
        , "--llvm-kompile-type"
        , "c"
        , "--syntax-module"
        , "LLVM"
        , "-o"
        , kompiledPath
        ]

loadAPI :: IO API
loadAPI = withDLib dlPath mkAPI

------------------------------------------------------------
-- term construction

boolSort, intSort, bytesSort, stringSort :: Sort
boolSort = SortApp "SortBool" []
intSort = SortApp "SortInt" []
bytesSort = SortApp "SortBytes" []
stringSort = SortApp "SortString" []

boolTerm :: Bool -> Term
boolTerm = DomainValue boolSort . BS.pack . map toLower . show

intTerm :: (Integral a, Show a) => a -> Term
intTerm = DomainValue intSort . BS.pack . show . (+ 0)

bytesTerm :: ByteString -> Term
bytesTerm = DomainValue bytesSort

equal :: (Integral a, Show a) => a -> a -> Term
a `equal` b = SymbolApplication eqInt [] [intTerm a, intTerm b]
  where
    eqInt =
        fromMaybe (error "missing symbol") $
            Map.lookup "Lbl'UndsEqlsEqls'Int'Unds'" defSymbols

-- Definition from test/llvm/llvm.k

testDef :: KoreDefinition
testDef =
    KoreDefinition
        DefinitionAttributes
        Map.empty -- no modules (HACK)
        defSorts
        defSymbols
        Map.empty -- no aliases
        Map.empty -- no rules
        Map.empty -- no function equations
        Map.empty -- no simplifications
        Map.empty -- no ceils

{- To refresh the definition below, run this using the repl and fix up
   the remainder of the file if differences are shown.
-}
displayTestDef :: IO ()
displayTestDef = do
    defText <- Text.readFile (kompiledPath </> "definition.kore")
    parsed <- either error pure $ parseDefinition definition defText
    defMap <- either (error . show) pure $ runExcept $ buildDefinitions parsed
    let def = fromMaybe (error "LLVM module not found") $ Map.lookup "LLVM" defMap
        prunedDef =
            def
                { modules = Map.empty
                , aliases = Map.empty
                , functionEquations = Map.empty
                , simplifications = Map.empty
                }
    -- compare to what we have
    if testDef == prunedDef
        then putStrLn "Definition in Haskell file is consistent with compilation output"
        else do
            putStrLn "Differences between Haskell file and loaded definition:"
            when (testDef.sorts /= prunedDef.sorts) $ do
                putStrLn "sorts differ"
                mapCompare testDef.sorts prunedDef.sorts
            when (testDef.symbols /= prunedDef.symbols) $ do
                putStrLn "symbols differ"
                mapCompare testDef.symbols prunedDef.symbols
  where
    mapCompare map1 map2 = do
        let diff1 = Map.difference map1 map2
            diff2 = Map.difference map2 map1
            commonKeys = Set.intersection (Map.keysSet map1) (Map.keysSet map2)
        let elemCompare k =
                let e1 = fromMaybe (error "Bad key") $ Map.lookup k map1
                    e2 = fromMaybe (error "Bad key") $ Map.lookup k map2
                 in when (e1 /= e2) $ do
                        putStrLn $ "Elements at key " <> show k <> " differ:"
                        print e1
                        print e2
        mapM_ elemCompare commonKeys
        unless (Map.null diff1) $
            putStrLn $
                "Map 1 has additional keys " <> show (Set.toList $ Map.keysSet diff1)
        unless (Map.null diff2) $
            putStrLn $
                "Map 2 has additional keys " <> show (Set.toList $ Map.keysSet diff2)

sortMapKmap :: KMapDefinition
sortMapKmap =
    KMapDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'Map"
                , elementSymbolName = "Lbl'UndsPipe'-'-GT-Unds'"
                , concatSymbolName = "Lbl'Unds'Map'Unds'"
                }
        , keySortName = "SortKItem"
        , elementSortName = "SortKItem"
        , mapSortName = "SortMap"
        }

sortListKList :: KListDefinition
sortListKList =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'List"
                , elementSymbolName = "LblListItem"
                , concatSymbolName = "Lbl'Unds'List'Unds'"
                }
        , elementSortName = "SortKItem"
        , listSortName = "SortList"
        }

defSorts :: Map SortName (SortAttributes, Set SortName)
defSorts =
    Map.fromList
        [
            ( "SortBool"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortBool"])
            )
        ,
            ( "SortBytes"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortBytes"])
            )
        ,
            ( "SortEndianness"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortEndianness"])
            )
        ,
            ( "SortEven"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortEven"])
            )
        ,
            ( "SortGeneratedCounterCell"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortGeneratedCounterCell"]
                )
            )
        ,
            ( "SortGeneratedCounterCellOpt"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortGeneratedCounterCell", "SortGeneratedCounterCellOpt"]
                )
            )
        ,
            ( "SortGeneratedTopCell"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortGeneratedTopCell"]
                )
            )
        ,
            ( "SortGeneratedTopCellFragment"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortGeneratedTopCellFragment"]
                )
            )
        ,
            ( "SortInt"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortInt"])
            )
        , ("SortK", (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortK"]))
        ,
            ( "SortKCell"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortKCell"])
            )
        ,
            ( "SortKCellOpt"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortKCell", "SortKCellOpt"]
                )
            )
        ,
            ( "SortKConfigVar"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortKConfigVar"])
            )
        ,
            ( "SortKItem"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList
                    [ "SortBool"
                    , "SortBytes"
                    , "SortEndianness"
                    , "SortEven"
                    , "SortGeneratedCounterCell"
                    , "SortGeneratedCounterCellOpt"
                    , "SortGeneratedTopCell"
                    , "SortGeneratedTopCellFragment"
                    , "SortInt"
                    , "SortKCell"
                    , "SortKCellOpt"
                    , "SortKConfigVar"
                    , "SortKItem"
                    , "SortList"
                    , "SortMap"
                    , "SortNum"
                    , "SortOdd"
                    , "SortSet"
                    , "SortSignedness"
                    , "SortString"
                    ]
                )
            )
        ,
            ( "SortList"
            ,
                ( SortAttributes{collectionAttributes = Just (sortListKList.symbolNames, KListTag), argCount = 0}
                , Set.fromList ["SortList"]
                )
            )
        ,
            ( "SortMap"
            ,
                ( SortAttributes{collectionAttributes = Just (sortMapKmap.symbolNames, KMapTag), argCount = 0}
                , Set.fromList ["SortMap"]
                )
            )
        ,
            ( "SortNum"
            ,
                ( SortAttributes{collectionAttributes = Nothing, argCount = 0}
                , Set.fromList ["SortEven", "SortNum", "SortOdd"]
                )
            )
        ,
            ( "SortOdd"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortOdd"])
            )
        ,
            ( "SortSet"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortSet"])
            )
        ,
            ( "SortSignedness"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortSignedness"])
            )
        ,
            ( "SortString"
            , (SortAttributes{collectionAttributes = Nothing, argCount = 0}, Set.fromList ["SortString"])
            )
        ]

defSymbols :: Map SymbolName Symbol
defSymbols =
    Map.fromList
        [
            ( "Lbl'-LT-'generatedCounter'-GT-'"
            , Symbol
                { name = "Lbl'-LT-'generatedCounter'-GT-'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortGeneratedCounterCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'-LT-'generatedTop'-GT-'"
            , Symbol
                { name = "Lbl'-LT-'generatedTop'-GT-'"
                , sortVars = []
                , argSorts = [SortApp "SortKCell" [], SortApp "SortGeneratedCounterCell" []]
                , resultSort = SortApp "SortGeneratedTopCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'-LT-'generatedTop'-GT-'-fragment"
            , Symbol
                { name = "Lbl'-LT-'generatedTop'-GT-'-fragment"
                , sortVars = []
                , argSorts = [SortApp "SortKCellOpt" [], SortApp "SortGeneratedCounterCellOpt" []]
                , resultSort = SortApp "SortGeneratedTopCellFragment" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'-LT-'k'-GT-'"
            , Symbol
                { name = "Lbl'-LT-'k'-GT-'"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortKCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
            , Symbol
                { name =
                    "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
                , sortVars = ["SortSort"]
                , argSorts = [SortApp "SortBool" [], SortVar "SortSort", SortVar "SortSort"]
                , resultSort = SortVar "SortSort"
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Stop'Bytes'Unds'BYTES-HOOKED'Unds'Bytes"
            , Symbol
                { name = "Lbl'Stop'Bytes'Unds'BYTES-HOOKED'Unds'Bytes"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Stop'List"
            , Symbol
                { name = "Lbl'Stop'List"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KListMeta sortListKList
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Stop'Map"
            , Symbol
                { name = "Lbl'Stop'Map"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KMapMeta sortMapKmap
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Stop'Set"
            , Symbol
                { name = "Lbl'Stop'Set"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Tild'Int'Unds'"
            , Symbol
                { name = "Lbl'Tild'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'-Int'Unds'"
            , Symbol
                { name = "Lbl'Unds'-Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map"
            , Symbol
                { name = "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortMap" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'List'Unds'"
            , Symbol
                { name = "Lbl'Unds'List'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortList" [], SortApp "SortList" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KListMeta sortListKList
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'Map'Unds'"
            , Symbol
                { name = "Lbl'Unds'Map'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortMap" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KMapMeta sortMapKmap
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'Set'Unds'"
            , Symbol
                { name = "Lbl'Unds'Set'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortSet" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsIdem
                        , isAssoc = IsAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'andBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'andBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'andThenBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'andThenBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'divInt'Unds'"
            , Symbol
                { name = "Lbl'Unds'divInt'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"
            , Symbol
                { name = "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'impliesBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'impliesBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"
            , Symbol
                { name = "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" [], SortApp "SortMap" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'in'UndsUnds'LIST'Unds'Bool'Unds'KItem'Unds'List"
            , Symbol
                { name = "Lbl'Unds'in'UndsUnds'LIST'Unds'Bool'Unds'KItem'Unds'List"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" [], SortApp "SortList" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'modInt'Unds'"
            , Symbol
                { name = "Lbl'Unds'modInt'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'orBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'orBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'orElseBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'orElseBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'xorBool'Unds'"
            , Symbol
                { name = "Lbl'Unds'xorBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds'xorInt'Unds'"
            , Symbol
                { name = "Lbl'Unds'xorInt'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-GT-'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-GT-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-GT--GT-'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-GT--GT-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-GT-Eqls'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-GT-Eqls'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-LT-'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-LT-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-LT--LT-'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-LT--LT-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-LT-Eqls'Int'Unds'"
            , Symbol
                { name = "Lbl'Unds-LT-Eqls'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map"
            , Symbol
                { name = "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortMap" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set"
            , Symbol
                { name = "Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortSet" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsAnd-'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsAnd-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsEqls'Bool'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsEqls'Bool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsEqls'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsEqls'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsEqls'K'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsEqls'K'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortK" [], SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsSlshEqls'Bool'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsSlshEqls'Bool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" [], SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsSlshEqls'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsSlshEqls'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsEqlsSlshEqls'K'Unds'"
            , Symbol
                { name = "Lbl'UndsEqlsSlshEqls'K'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortK" [], SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
            , Symbol
                { name = "Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'KItem"
            , Symbol
                { name = "Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'KItem"
                , sortVars = []
                , argSorts = [SortApp "SortList" [], SortApp "SortInt" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsLSqBUnds-LT-'-undef'RSqB'"
            , Symbol
                { name = "Lbl'UndsLSqBUnds-LT-'-undef'RSqB'"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsLSqBUndsRSqB'orDefault'UndsUnds'MAP'Unds'KItem'Unds'Map'Unds'KItem'Unds'KItem"
            , Symbol
                { name = "Lbl'UndsLSqBUndsRSqB'orDefault'UndsUnds'MAP'Unds'KItem'Unds'Map'Unds'KItem'Unds'KItem"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortKItem" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsLSqBUndsRSqBUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Int"
            , Symbol
                { name = "Lbl'UndsLSqBUndsRSqBUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPerc'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsPerc'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPipe'-'-GT-Unds'"
            , Symbol
                { name = "Lbl'UndsPipe'-'-GT-Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KMapMeta sortMapKmap
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPipe'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsPipe'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set"
            , Symbol
                { name = "Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortSet" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPlus'Bytes'UndsUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Bytes"
            , Symbol
                { name = "Lbl'UndsPlus'Bytes'UndsUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortBytes" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsPlus'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsPlus'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsSlsh'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsSlsh'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsStar'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsStar'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsXor-'Int'Unds'"
            , Symbol
                { name = "Lbl'UndsXor-'Int'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbl'UndsXor-Perc'Int'UndsUnds'"
            , Symbol
                { name = "Lbl'UndsXor-Perc'Int'UndsUnds'"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblBytes2Int'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Endianness'Unds'Signedness"
            , Symbol
                { name =
                    "LblBytes2Int'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Endianness'Unds'Signedness"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortEndianness" [], SortApp "SortSignedness" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes"
            , Symbol
                { name = "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" []]
                , resultSort = SortApp "SortString" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblEight'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblEight'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblFive'LParRParUnds'LLVM'Unds'Odd"
            , Symbol
                { name = "LblFive'LParRParUnds'LLVM'Unds'Odd"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblFour'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblFour'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Endianness'Unds'Signedness"
            , Symbol
                { name =
                    "LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Endianness'Unds'Signedness"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortEndianness" [], SortApp "SortSignedness" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Int'Unds'Endianness"
            , Symbol
                { name =
                    "LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Int'Unds'Endianness"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" [], SortApp "SortEndianness" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblList'Coln'get"
            , Symbol
                { name = "LblList'Coln'get"
                , sortVars = []
                , argSorts = [SortApp "SortList" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblList'Coln'range"
            , Symbol
                { name = "LblList'Coln'range"
                , sortVars = []
                , argSorts = [SortApp "SortList" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblListItem"
            , Symbol
                { name = "LblListItem"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Just $ KListMeta sortListKList
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblMap'Coln'lookup"
            , Symbol
                { name = "LblMap'Coln'lookup"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblMap'Coln'update"
            , Symbol
                { name = "LblMap'Coln'update"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortKItem" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblNine'LParRParUnds'LLVM'Unds'Odd"
            , Symbol
                { name = "LblNine'LParRParUnds'LLVM'Unds'Odd"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblOne'LParRParUnds'LLVM'Unds'Odd"
            , Symbol
                { name = "LblOne'LParRParUnds'LLVM'Unds'Odd"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblSet'Coln'difference"
            , Symbol
                { name = "LblSet'Coln'difference"
                , sortVars = []
                , argSorts = [SortApp "SortSet" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblSet'Coln'in"
            , Symbol
                { name = "LblSet'Coln'in"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblSetItem"
            , Symbol
                { name = "LblSetItem"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblSeven'LParRParUnds'LLVM'Unds'Odd"
            , Symbol
                { name = "LblSeven'LParRParUnds'LLVM'Unds'Odd"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblSix'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblSix'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String"
            , Symbol
                { name = "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String"
                , sortVars = []
                , argSorts = [SortApp "SortString" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblTen'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblTen'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblThree'LParRParUnds'LLVM'Unds'Odd"
            , Symbol
                { name = "LblThree'LParRParUnds'LLVM'Unds'Odd"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblTwo'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblTwo'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblZero'LParRParUnds'LLVM'Unds'Even"
            , Symbol
                { name = "LblZero'LParRParUnds'LLVM'Unds'Even"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
            , Symbol
                { name = "LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblbigEndianBytes"
            , Symbol
                { name = "LblbigEndianBytes"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEndianness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int"
            , Symbol
                { name =
                    "LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblchoice'LParUndsRParUnds'MAP'Unds'KItem'Unds'Map"
            , Symbol
                { name = "Lblchoice'LParUndsRParUnds'MAP'Unds'KItem'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblchoice'LParUndsRParUnds'SET'Unds'KItem'Unds'Set"
            , Symbol
                { name = "Lblchoice'LParUndsRParUnds'SET'Unds'KItem'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortSet" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbldiv2'LParUndsRParUnds'LLVM'Unds'Num'Unds'Even"
            , Symbol
                { name = "Lbldiv2'LParUndsRParUnds'LLVM'Unds'Num'Unds'Even"
                , sortVars = []
                , argSorts = [SortApp "SortEven" []]
                , resultSort = SortApp "SortNum" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbleval'LParUndsRParUnds'LLVM'Unds'Int'Unds'Num"
            , Symbol
                { name = "Lbleval'LParUndsRParUnds'LLVM'Unds'Int'Unds'Num"
                , sortVars = []
                , argSorts = [SortApp "SortNum" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblfillList'LParUndsCommUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'Int'Unds'KItem"
            , Symbol
                { name =
                    "LblfillList'LParUndsCommUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'Int'Unds'KItem"
                , sortVars = []
                , argSorts =
                    [SortApp "SortList" [], SortApp "SortInt" [], SortApp "SortInt" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int"
            , Symbol
                { name = "LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblgetGeneratedCounterCell"
            , Symbol
                { name = "LblgetGeneratedCounterCell"
                , sortVars = []
                , argSorts = [SortApp "SortGeneratedTopCell" []]
                , resultSort = SortApp "SortGeneratedCounterCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblinitGeneratedCounterCell"
            , Symbol
                { name = "LblinitGeneratedCounterCell"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortGeneratedCounterCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblinitGeneratedTopCell"
            , Symbol
                { name = "LblinitGeneratedTopCell"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortGeneratedTopCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblinitKCell"
            , Symbol
                { name = "LblinitKCell"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortKCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set"
            , Symbol
                { name = "LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortSet" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisBool"
            , Symbol
                { name = "LblisBool"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisBytes"
            , Symbol
                { name = "LblisBytes"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisEndianness"
            , Symbol
                { name = "LblisEndianness"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisEven"
            , Symbol
                { name = "LblisEven"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisGeneratedCounterCell"
            , Symbol
                { name = "LblisGeneratedCounterCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisGeneratedCounterCellOpt"
            , Symbol
                { name = "LblisGeneratedCounterCellOpt"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisGeneratedTopCell"
            , Symbol
                { name = "LblisGeneratedTopCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisGeneratedTopCellFragment"
            , Symbol
                { name = "LblisGeneratedTopCellFragment"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisInt"
            , Symbol
                { name = "LblisInt"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisK"
            , Symbol
                { name = "LblisK"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisKCell"
            , Symbol
                { name = "LblisKCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisKCellOpt"
            , Symbol
                { name = "LblisKCellOpt"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisKConfigVar"
            , Symbol
                { name = "LblisKConfigVar"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisKItem"
            , Symbol
                { name = "LblisKItem"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisList"
            , Symbol
                { name = "LblisList"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisMap"
            , Symbol
                { name = "LblisMap"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisNum"
            , Symbol
                { name = "LblisNum"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisOdd"
            , Symbol
                { name = "LblisOdd"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisSet"
            , Symbol
                { name = "LblisSet"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisSignedness"
            , Symbol
                { name = "LblisSignedness"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblisString"
            , Symbol
                { name = "LblisString"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map"
            , Symbol
                { name = "Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map"
            , Symbol
                { name = "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LbllengthBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes"
            , Symbol
                { name = "LbllengthBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LbllittleEndianBytes"
            , Symbol
                { name = "LbllittleEndianBytes"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortEndianness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
            , Symbol
                { name = "Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblmakeList'LParUndsCommUndsRParUnds'LIST'Unds'List'Unds'Int'Unds'KItem"
            , Symbol
                { name = "LblmakeList'LParUndsCommUndsRParUnds'LIST'Unds'List'Unds'Int'Unds'KItem"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortKItem" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int"
            , Symbol
                { name = "LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int"
            , Symbol
                { name = "LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblnoGeneratedCounterCell"
            , Symbol
                { name = "LblnoGeneratedCounterCell"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortGeneratedCounterCellOpt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblnoKCell"
            , Symbol
                { name = "LblnoKCell"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortKCellOpt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblnotBool'Unds'"
            , Symbol
                { name = "LblnotBool'Unds'"
                , sortVars = []
                , argSorts = [SortApp "SortBool" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblpadLeftBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
            , Symbol
                { name =
                    "LblpadLeftBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblpadRightBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
            , Symbol
                { name =
                    "LblpadRightBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblpred'LParUndsRParUnds'LLVM'Unds'Num'Unds'Num"
            , Symbol
                { name = "Lblpred'LParUndsRParUnds'LLVM'Unds'Num'Unds'Num"
                , sortVars = []
                , argSorts = [SortApp "SortNum" []]
                , resultSort = SortApp "SortNum" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Bool"
            , Symbol
                { name = "Lblproject'Coln'Bool"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBool" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Bytes"
            , Symbol
                { name = "Lblproject'Coln'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Endianness"
            , Symbol
                { name = "Lblproject'Coln'Endianness"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortEndianness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Even"
            , Symbol
                { name = "Lblproject'Coln'Even"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortEven" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'GeneratedCounterCell"
            , Symbol
                { name = "Lblproject'Coln'GeneratedCounterCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortGeneratedCounterCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'GeneratedCounterCellOpt"
            , Symbol
                { name = "Lblproject'Coln'GeneratedCounterCellOpt"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortGeneratedCounterCellOpt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'GeneratedTopCell"
            , Symbol
                { name = "Lblproject'Coln'GeneratedTopCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortGeneratedTopCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'GeneratedTopCellFragment"
            , Symbol
                { name = "Lblproject'Coln'GeneratedTopCellFragment"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortGeneratedTopCellFragment" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Int"
            , Symbol
                { name = "Lblproject'Coln'Int"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'K"
            , Symbol
                { name = "Lblproject'Coln'K"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortK" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'KCell"
            , Symbol
                { name = "Lblproject'Coln'KCell"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortKCell" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'KCellOpt"
            , Symbol
                { name = "Lblproject'Coln'KCellOpt"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortKCellOpt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'KItem"
            , Symbol
                { name = "Lblproject'Coln'KItem"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortKItem" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'List"
            , Symbol
                { name = "Lblproject'Coln'List"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Map"
            , Symbol
                { name = "Lblproject'Coln'Map"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Num"
            , Symbol
                { name = "Lblproject'Coln'Num"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortNum" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Odd"
            , Symbol
                { name = "Lblproject'Coln'Odd"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortOdd" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Set"
            , Symbol
                { name = "Lblproject'Coln'Set"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortSet" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'Signedness"
            , Symbol
                { name = "Lblproject'Coln'Signedness"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortSignedness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblproject'Coln'String"
            , Symbol
                { name = "Lblproject'Coln'String"
                , sortVars = []
                , argSorts = [SortApp "SortK" []]
                , resultSort = SortApp "SortString" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
            , Symbol
                { name = "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set"
            , Symbol
                { name = "LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortSet" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblreplaceAtBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Bytes"
            , Symbol
                { name =
                    "LblreplaceAtBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" [], SortApp "SortBytes" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblreverseBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes"
            , Symbol
                { name = "LblreverseBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int"
            , Symbol
                { name =
                    "LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblsignedBytes"
            , Symbol
                { name = "LblsignedBytes"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortSignedness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblsize'LParUndsRParUnds'LIST'Unds'Int'Unds'List"
            , Symbol
                { name = "Lblsize'LParUndsRParUnds'LIST'Unds'Int'Unds'List"
                , sortVars = []
                , argSorts = [SortApp "SortList" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblsize'LParUndsRParUnds'MAP'Unds'Int'Unds'Map"
            , Symbol
                { name = "Lblsize'LParUndsRParUnds'MAP'Unds'Int'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set"
            , Symbol
                { name = "Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set"
                , sortVars = []
                , argSorts = [SortApp "SortSet" []]
                , resultSort = SortApp "SortInt" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int"
            , Symbol
                { name = "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortInt" []]
                , resultSort = SortApp "SortK" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblsubstrBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
            , Symbol
                { name =
                    "LblsubstrBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int"
                , sortVars = []
                , argSorts = [SortApp "SortBytes" [], SortApp "SortInt" [], SortApp "SortInt" []]
                , resultSort = SortApp "SortBytes" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblunsignedBytes"
            , Symbol
                { name = "LblunsignedBytes"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortSignedness" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblupdateList'LParUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'List"
            , Symbol
                { name = "LblupdateList'LParUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'List"
                , sortVars = []
                , argSorts = [SortApp "SortList" [], SortApp "SortInt" [], SortApp "SortList" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map"
            , Symbol
                { name = "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" [], SortApp "SortMap" []]
                , resultSort = SortApp "SortMap" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map"
            , Symbol
                { name = "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map"
                , sortVars = []
                , argSorts = [SortApp "SortMap" []]
                , resultSort = SortApp "SortList" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = PartialFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "append"
            , Symbol
                { name = "append"
                , sortVars = []
                , argSorts = [SortApp "SortK" [], SortApp "SortK" []]
                , resultSort = SortApp "SortK" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = TotalFunction
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "dotk"
            , Symbol
                { name = "dotk"
                , sortVars = []
                , argSorts = []
                , resultSort = SortApp "SortK" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "inj"
            , Symbol
                { name = "inj"
                , sortVars = ["From", "To"]
                , argSorts = [SortVar "From"]
                , resultSort = SortVar "To"
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = SortInjection
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "kseq"
            , Symbol
                { name = "kseq"
                , sortVars = []
                , argSorts = [SortApp "SortKItem" [], SortApp "SortK" []]
                , resultSort = SortApp "SortK" []
                , attributes =
                    SymbolAttributes
                        { collectionMetadata = Nothing
                        , symbolType = Constructor
                        , isIdem = IsNotIdem
                        , isAssoc = IsNotAssoc
                        , isMacroOrAlias = IsNotMacroOrAlias
                        , hasEvaluators = CanBeEvaluated
                        , smt = Nothing
                        , hook = Nothing
                        }
                }
            )
        ,
            ( "LblwrapInt"
            , [symb| symbol LblwrapInt{}(SortInt{}) : SortWrappedInt{} [constructor{}(), functional{}(), injective{}()] |]
            )
        ,
            ( "Lbl'Stop'MapValToVal"
            , [symb| symbol Lbl'Stop'MapValToVal{}() : SortMapValToVal{} [function{}(), functional{}(), total{}()] |]
            )
        ,
            ( "LblMapValToVal'Coln'primitiveUpdate"
            , [symb| symbol LblMapValToVal'Coln'primitiveUpdate{}(SortMapValToVal{}, SortVal{}, SortVal{}) : SortMapValToVal{} [function{}(), functional{}(), klabel{}("MapValToVal:primitiveUpdate"), total{}()] |]
            )
        ,
            ( "Lbl'Unds'Val2Val'Pipe'-'-GT-Unds'"
            , [symb| symbol Lbl'Unds'Val2Val'Pipe'-'-GT-Unds'{}(SortVal{}, SortVal{}) : SortMapValToVal{} [function{}(), functional{}(), klabel{}("_Val2Val|->_"), total{}()] |]
            )
        ]
