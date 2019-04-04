{-|
Module      : Kore.Step.SMT.Sorts
Description : Declares sorts to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Sorts
    ( translateSort
    , declareSorts
    ) where

import           Control.Monad
                 ( zipWithM )
import           Data.Either
                 ( partitionEithers )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Reflection
                 ( Given, given )
import qualified Data.Set as Set
import           Data.Text
                 ( Text, isPrefixOf, pack )

import           Kore.AST.Common
                 ( SymbolOrAlias (SymbolOrAlias), Variable (Variable) )
import           Kore.AST.Common as SymbolOrAlias
                 ( SymbolOrAlias (..) )
import qualified Kore.AST.Common as Variable
                 ( Variable (..) )
import           Kore.AST.Identifier
                 ( Id (getId) )
import           Kore.AST.Kore
                 ( KorePattern, VerifiedKorePattern )
import           Kore.AST.MetaOrObject
                 ( Object (Object), Unified )
import           Kore.AST.Sentence
                 ( SentenceAxiom (SentenceAxiom), SentenceSort (SentenceSort) )
import qualified Kore.AST.Sentence as SentenceSort
                 ( SentenceSort (..) )
import qualified Kore.AST.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import           Kore.AST.Valid
                 ( pattern App_, pattern Bottom_, pattern Exists_, pattern Or_,
                 Valid, pattern Var_ )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Axiom.Constructor as Axiom.Constructor
import           Kore.Attribute.Hook.Hook
                 ( Hook (Hook) )
import qualified Kore.Attribute.Hook.Hook as Hook
import           Kore.Attribute.Smtlib
                 ( applySExpr )
import           Kore.Attribute.Smtlib.Smtlib
                 ( Smtlib (Smtlib) )
import qualified Kore.Attribute.Smtlib.Smtlib as Smtlib
import qualified Kore.Attribute.Sort as Attribute
import           Kore.Attribute.Symbol
                 ( Symbol )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Int as Int
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule, recursiveIndexedModuleAxioms,
                 recursiveIndexedModuleSortDescriptions )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (sortAttributes) )
import           Kore.Sort
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )
import           Kore.Step.Pattern
                 ( CommonStepPattern, fromKorePattern )
import           Kore.Step.SMT.Encoder
                 ( encodeName )
import           Kore.Unparser
                 ( unparseToString )
import qualified SMT

data SMTConstructor =
    SMTConstructor
        { name :: Text
        , argumentSorts :: [Sort Object]
        }
    deriving (Eq, Show)

data SMTDataType =
    SMTDataType
        { sort :: Sort Object
        , constructors :: [ SMTConstructor ]
        }
    deriving (Eq, Show)

{-| Translate a sort into an SMT s-expression.

Not all cases are implemented. `translateSort` should fail for all cases that
are not implemented by `declareSorts`.
-}
translateSort
    :: Given (MetadataTools Object Symbol)
    => Sort Object
    -> Maybe SMT.SExpr
translateSort sort@(SortActualSort (SortActual sortId children))
  | Just s <- getHook
  , s == Int.sort
    = return SMT.tInt
  | Just s <- getHook
  , s == Bool.sort
    = return SMT.tBool
  | Just sExpr <- getSmtlib = do
    children' <- mapM translateSort children
    return $ applySExpr sExpr children'
  | "#" `isPrefixOf` getId sortId =
    -- filter out old meta sorts which get included automatically in
    -- definitions.
    Nothing
  | null children =
    return (SMT.Atom $ encodeName (getId sortId))
  | otherwise = Nothing  -- TODO(virgil): Handle parametric sorts.

  where
    tools :: MetadataTools Object Symbol
    tools = given
    attrs = sortAttributes tools sort
    Attribute.Sort { hook = Hook { getHook } } = attrs
    Attribute.Sort { smtlib = Smtlib { getSmtlib } } = attrs
translateSort _ = Nothing

translateSortName
    :: Given (MetadataTools Object Symbol)
    => Sort Object
    -> Maybe Text
translateSortName sort = do
    sExp <- translateSort sort
    case sExp of
        SMT.Atom name -> return name
        SMT.List (SMT.Atom name : _) -> return name
        _ -> (error . unlines)
            [ "Unrecognized sort representation."
            , "sort=" ++ unparseToString sort
            , "representation=" ++ SMT.showSExpr sExp
            ]

{-| Declares sorts for the SMT.

Not all cases are implemented. `translateSort` should fail for all cases that
are not implemented here.
-}
declareSorts
    ::  ( Given (MetadataTools Object Symbol)
        , SMT.MonadSMT m
        )
    => IndexedModule
        param
        (KorePattern
            Domain.Builtin
            Variable
            (Unified (Valid (Unified Variable)))
        )
        Symbol
        Attribute.Axiom
    -> m ()
declareSorts indexedModule = do
    -- TODO: Filter out meta sorts like '#Char'
    let
        noJunkAxioms :: [SMTDataType]
        noJunkAxioms = parseNoJunkAxioms indexedModule

        nameToSMTDataType :: Map.Map Text SMTDataType
        nameToSMTDataType =
            foldr addToMap Map.empty noJunkAxioms
          where
            addToMap
                axiom@SMTDataType
                    { sort = SortActualSort SortActual {sortActualName} }
                axioms
              =
                case Map.lookup sortName axioms of
                    Nothing -> Map.insert sortName axiom axioms
                    Just _ -> error ("Two no-junk axioms for " ++ show sortName)
              where
                sortName = getId sortActualName
            addToMap axiom _ = error
                ("Unexpected no-junk axiom for sort variable: " ++ show axiom)

        sortDeclarations
            :: [(Attribute.Sort, SentenceSort Object VerifiedKorePattern)]
        sortDeclarations =
            Map.elems (recursiveIndexedModuleSortDescriptions indexedModule)

        (declarationsWithoutNoJunk, declarationsWithNoJunk) =
            partitionEithers (map splitDeclarationsWorker sortDeclarations)
          where
            splitDeclarationsWorker
                (attribute, sentence@SentenceSort {sentenceSortName})
              = case Map.lookup (getId sentenceSortName) nameToSMTDataType of
                Nothing -> Left (attribute, sentence)
                Just noJunk -> Right (attribute, sentence, noJunk)

    mapM_
        declareSortWithoutNoJunkAxiom
        declarationsWithoutNoJunk

    declareSortsWithNoJunkAxioms declarationsWithNoJunk

declareSortWithoutNoJunkAxiom
    ::  ( Given (MetadataTools Object Symbol)
        , SMT.MonadSMT m
        )
    => (Attribute.Sort, SentenceSort Object pat)
    -> m ()
declareSortWithoutNoJunkAxiom
    ( attributes
    , SentenceSort {sentenceSortName, sentenceSortParameters}
    )
  =
    case (getSmtlib, getHook) of
        (Just (SMT.List (SMT.Atom name : sortArgs)), _)-> do
            _ <- SMT.declareSort name (length sortArgs)
            return ()
        (Just sexpression, _) ->
            error ("Unrecognized smtlib: " ++ show sexpression)
        (Nothing, Just name)
          | name == Int.sort ->
            return ()
          | name == Bool.sort ->
            return ()
        _
          | null sentenceSortParameters ->
            case translateSortName sortForTranslation of
                Just name -> do
                    _ <- SMT.declareSort name 0
                    return ()
                Nothing ->
                    return ()
          | otherwise ->
            -- TODO(virgil): Handle parametric sorts.
            return ()
  where
    Smtlib {getSmtlib} = Attribute.smtlib attributes
    Hook {getHook} = Attribute.hook attributes

    sortForTranslation :: Sort Object
    sortForTranslation =
        SortActualSort SortActual
            { sortActualName  = sentenceSortName
            , sortActualSorts = []
            }

declareSortsWithNoJunkAxioms
    ::  ( Given (MetadataTools Object Symbol)
        , SMT.MonadSMT m
        )
    => [(Attribute.Sort, SentenceSort Object pat, SMTDataType)]
    -> m ()
declareSortsWithNoJunkAxioms sorts =
    SMT.declareDatatypes (mapMaybe buildSort sorts)
  where
    buildSort
        ( attributes
        , SentenceSort {sentenceSortParameters}
        , SMTDataType { sort, constructors }
        )
      =
        case (getSmtlib, getHook, sentenceSortParameters) of
            (Nothing, Nothing, []) ->
                case (maybeSortName, maybeSmtConstructors) of
                    (Just sortName, Just smtConstructors) ->
                        Just (sortName, [], smtConstructors)
                    _ -> Nothing
            (Nothing, Nothing, _ : _) ->
                -- TODO(virgil): Handle parametric sorts.
                Nothing
            (_, _, _) -> (error . unlines)
                [ "Unexpected smtlib or hook together with no-junk axiom:"
                , "smtlib=" ++ show getSmtlib
                , "hook=" ++ show getHook
                , "sort=" ++ show sort
                ]
      where
        maybeSortName = translateSortName sort
        maybeSmtConstructors = mapM constructorToSmt constructors

        Smtlib {getSmtlib} = Attribute.smtlib attributes
        Hook {getHook} = Attribute.hook attributes

    constructorToSmt
        :: SMTConstructor -> Maybe (Text, [(Text, SMT.SExpr)])
    constructorToSmt
        SMTConstructor { name, argumentSorts }
      = do
        args <- zipWithM (constructorArgToSMT name) [1..] argumentSorts
        return (encodedName, args)
      where
        encodedName = encodeName name

    constructorArgToSMT
        :: Text -> Int -> Sort Object -> Maybe (Text, SMT.SExpr)
    constructorArgToSMT constrName index constrSort = do
        translatedSort <- translateSort constrSort
        return (encodeName (constrName <> pack (show index)), translatedSort)

parseNoJunkAxioms
    :: IndexedModule
        param
        (KorePattern
            Domain.Builtin
            Variable
            (Unified (Valid (Unified Variable)))
        )
        Symbol
        Attribute.Axiom
    -> [SMTDataType]
parseNoJunkAxioms indexedModule =
    filter (\ SMTDataType{constructors} -> not (null constructors))
    $ mapMaybe
        parseSMTDataType
        (recursiveIndexedModuleAxioms indexedModule)

parseSMTDataType
    ::  ( Attribute.Axiom
        , SentenceAxiom param VerifiedKorePattern
        )
    -> Maybe SMTDataType
parseSMTDataType (attributes, SentenceAxiom {sentenceAxiomPattern})
  | Axiom.Constructor.isConstructor (Attribute.constructor attributes)
  = case fromKorePattern Object sentenceAxiomPattern of
    Left err -> (error . unlines)
        [ "Unexpected error transforming kore pattern to pure pattern:"
        , " all patterns should be pure."
        , "err=" ++ show err
        , "pattern=" ++ show sentenceAxiomPattern
        ]
    Right patt -> parseSMTDataTypePattern patt
  | otherwise = Nothing

parseSMTDataTypePattern :: CommonStepPattern Object -> Maybe SMTDataType
parseSMTDataTypePattern (Bottom_ sort) =
    return SMTDataType
        { sort
        , constructors = []
        }
parseSMTDataTypePattern (Or_ _ first second) = do
    constructor <- parseSMTConstructor first
    SMTDataType {sort, constructors} <- parseSMTDataTypePattern second
    return SMTDataType
        { sort
        , constructors = constructor : constructors
        }
parseSMTDataTypePattern _ = Nothing

parseSMTConstructor
    :: CommonStepPattern Object -> Maybe SMTConstructor
parseSMTConstructor patt =
    case parsedPatt of
        App_ symbol children -> do
            childVariables <-
                checkOnlyQuantifiedVariablesOnce quantifiedVariables children
            buildConstructor symbol childVariables
        _ -> Nothing
  where
    (quantifiedVariables, parsedPatt) = parseExists patt

    parseExists
        :: CommonStepPattern Object
        -> (Set.Set (Variable Object), CommonStepPattern Object)
    parseExists (Exists_ _ variable child) =
        (Set.insert variable childVars, unquantifiedPatt)
      where
        (childVars, unquantifiedPatt) = parseExists child
    parseExists unquantifiedPatt = (Set.empty, unquantifiedPatt)

    checkOnlyQuantifiedVariablesOnce
        :: Set.Set (Variable Object)
        -> [CommonStepPattern Object]
        -> Maybe [Variable Object]
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        []
      | Set.null allowedVars = Just []
      | otherwise = Nothing
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        (patt0 : patts)
      = case patt0 of
        Var_ var ->
            if var `Set.member` allowedVars
                then do
                    vars <-
                        checkOnlyQuantifiedVariablesOnce
                            (Set.delete var allowedVars)
                            patts
                    return (var : vars)
                else Nothing
        _ -> Nothing

    buildConstructor
        :: SymbolOrAlias Object
        -> [Variable Object]
        -> Maybe SMTConstructor
    buildConstructor
        SymbolOrAlias { symbolOrAliasConstructor, symbolOrAliasParams = [] }
        childVariables
      = Just SMTConstructor
            { name = getId symbolOrAliasConstructor
            , argumentSorts = map parseVariableSort childVariables
            }
    -- TODO(virgil): Also handle parameterized symbols.
    buildConstructor _ _ = Nothing

    parseVariableSort :: Variable Object -> Sort Object
    parseVariableSort
        Variable { variableSort }
      = variableSort
