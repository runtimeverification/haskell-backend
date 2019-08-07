{-|
Module      : Kore.Step.SMT.Representation.Sorts
Description : Builds an SMT representation for sorts.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Representation.Sorts
    ( buildRepresentations
    ) where

import           Control.Monad
                 ( when, zipWithM )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set
import qualified Data.Text as Text

import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom )
import qualified Kore.Attribute.Axiom as Attribute.Axiom
                 ( constructor )
import qualified Kore.Attribute.Axiom.Constructor as Axiom.Constructor
import           Kore.Attribute.Hook
                 ( Hook (Hook) )
import qualified Kore.Attribute.Hook as Hook
import           Kore.Attribute.Smtlib
                 ( applySExpr )
import           Kore.Attribute.Smtlib.Smtlib
                 ( Smtlib (Smtlib) )
import qualified Kore.Attribute.Smtlib.Smtlib as Smtlib
import qualified Kore.Attribute.Sort as Attribute
                 ( Sort )
import qualified Kore.Attribute.Sort as Attribute.Sort
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Int as Int
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule, recursiveIndexedModuleAxioms,
                 recursiveIndexedModuleSortDescriptions )
import           Kore.Internal.TermLike
import           Kore.Sort
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )
import qualified Kore.Step.SMT.AST as AST
import           Kore.Syntax.Id
                 ( Id )
import           Kore.Syntax.Sentence
                 ( SentenceAxiom (SentenceAxiom), SentenceSort (SentenceSort) )
import qualified Kore.Syntax.Sentence as SentenceSort
                 ( SentenceSort (..) )
import qualified Kore.Syntax.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import           Kore.Unparser
                 ( unparseToString )
import qualified Kore.Verified as Verified
import qualified SMT
                 ( Constructor (Constructor),
                 ConstructorArgument (ConstructorArgument),
                 DataTypeDeclaration (DataTypeDeclaration), SExpr (Atom, List),
                 SortDeclaration (SortDeclaration), nameFromSExpr, showSExpr,
                 tBool, tInt )
import qualified SMT as SMT.DataTypeDeclaration
                 ( DataTypeDeclaration (..) )
import qualified SMT as SMT.SortDeclaration
                 ( SortDeclaration (..) )
import qualified SMT as SMT.ConstructorArgument
                 ( ConstructorArgument (..) )
import qualified SMT as SMT.Constructor
                 ( Constructor (..) )


translateSort
    :: Map.Map Id AST.SmtSort
    -> Sort
    -> Maybe SMT.SExpr
translateSort
    sorts
    (SortActualSort SortActual { sortActualName, sortActualSorts })
  = do
    AST.Sort { smtFromSortArgs } <- Map.lookup sortActualName sorts
    smtFromSortArgs sorts sortActualSorts
translateSort _ _ = Nothing

{-| Builds smt representations for sorts in the given module.

May ignore sorts that we don't handle yet (e.g. parameterized sorts).

All references to other sorts and symbols are left unresolved.
-}
buildRepresentations
    :: forall symbolAttribute
    .  VerifiedModule symbolAttribute Attribute.Axiom
    -> AST.UnresolvedDeclarations
buildRepresentations indexedModule =
    builtinAndSmtLibDeclarations
    `AST.mergePreferFirst`
        listToDeclarations (parseNoJunkAxioms builtinAndSmtLibSorts)
    `AST.mergePreferFirst`
        listToDeclarations simpleSortDeclarations
  where
    listToDeclarations
        :: [(Id, AST.UnresolvedSort)] -> AST.UnresolvedDeclarations
    listToDeclarations list =
        AST.Declarations
            { sorts = Map.fromList list
            , symbols = Map.empty
            }

    builtinAndSmtLibDeclarations :: AST.UnresolvedDeclarations
    builtinAndSmtLibDeclarations =
        listToDeclarations builtinSortDeclarations
        `AST.mergePreferFirst`
            listToDeclarations smtlibSortDeclarations

    builtinAndSmtLibSorts :: Set.Set Id
    builtinAndSmtLibSorts = Map.keysSet sorts
      where
        AST.Declarations {sorts} = builtinAndSmtLibDeclarations

    parseNoJunkAxioms
        :: Set.Set Id
        -> [(Id, AST.UnresolvedSort)]
    parseNoJunkAxioms blacklist =
        filter
            (not . (`Set.member` blacklist) . fst)
            (mapMaybe
                parseNoJunkAxiom
                (recursiveIndexedModuleAxioms indexedModule)
            )

    builtinSortDeclarations :: [(Id, AST.UnresolvedSort)]
    builtinSortDeclarations =
        extractDefinitionsFromSentences builtinSortDeclaration

    smtlibSortDeclarations :: [(Id, AST.UnresolvedSort)]
    smtlibSortDeclarations =
        extractDefinitionsFromSentences smtlibSortDeclaration

    simpleSortDeclarations :: [(Id, AST.UnresolvedSort)]
    simpleSortDeclarations =
        extractDefinitionsFromSentences simpleSortDeclaration

    extractDefinitionsFromSentences
        ::  (   ( Attribute.Sort
                , Verified.SentenceSort
                )
            -> Maybe (Id, AST.UnresolvedSort)
            )
        -> [(Id, AST.UnresolvedSort)]
    extractDefinitionsFromSentences definitionExtractor =
        mapMaybe
            definitionExtractor
            (Map.elems $ recursiveIndexedModuleSortDescriptions indexedModule)

builtinSortDeclaration
    ::  ( Attribute.Sort
        , Verified.SentenceSort
        )
    -> Maybe (Id, AST.UnresolvedSort)
builtinSortDeclaration
    (attributes, SentenceSort { sentenceSortName })
  = do
    smtRepresentation <- case getHook of
        Just name
            | name == Int.sort -> return SMT.tInt
            | name == Bool.sort -> return SMT.tBool
        _ -> Nothing
    return
        ( sentenceSortName
        , AST.Sort
            { smtFromSortArgs = emptySortArgsToSmt smtRepresentation
            , declaration =
                AST.SortDeclaredIndirectly
                    (AST.AlreadyEncoded (SMT.nameFromSExpr smtRepresentation))
            }
        )
  where
    Hook {getHook} = Attribute.Sort.hook attributes

smtlibSortDeclaration
    ::  ( Attribute.Sort
        , Verified.SentenceSort
        )
    -> Maybe (Id, AST.UnresolvedSort)
smtlibSortDeclaration
    (attributes, SentenceSort { sentenceSortName })
  = do
    smtRepresentation@(SMT.List (SMT.Atom smtName : sortArgs)) <- getSmtlib
    return
        ( sentenceSortName
        , AST.Sort
            { smtFromSortArgs = applyToArgs smtRepresentation
            , declaration = AST.SortDeclarationSort
                SMT.SortDeclaration
                    { name = AST.AlreadyEncoded smtName
                    , arity = length sortArgs
                    }
            }
        )
  where
    applyToArgs
        :: SMT.SExpr
        -> Map.Map Id AST.SmtSort
        -> [Sort]
        -> Maybe SMT.SExpr
    applyToArgs sExpr definitions children = do
        children' <- mapM (translateSort definitions) children
        return $ applySExpr sExpr children'
    Smtlib { getSmtlib } = Attribute.Sort.smtlib attributes

simpleSortDeclaration
    ::  ( Attribute.Sort
        , Verified.SentenceSort
        )
    -> Maybe (Id, AST.UnresolvedSort)
simpleSortDeclaration
    ( _attribute
    , SentenceSort
        { sentenceSortName
        , sentenceSortParameters = []
        }
    )
  = Just
        ( sentenceSortName
        , AST.Sort
            { smtFromSortArgs =
                emptySortArgsToSmt (SMT.Atom $ AST.encode encodedName)
            , declaration = AST.SortDeclarationSort
                SMT.SortDeclaration
                    { name = encodedName
                    , arity = 0
                    }
            }
        )
  where
    encodedName = AST.encodable sentenceSortName
simpleSortDeclaration _ = Nothing

emptySortArgsToSmt
    :: SMT.SExpr
    -> Map.Map Id AST.SmtSort
    -> [Sort]
    -> Maybe SMT.SExpr
emptySortArgsToSmt representation _ [] = Just representation
emptySortArgsToSmt representation _ args = (error . unlines)
    [ "Sorts with arguments not supported yet."
    , "representation=" ++ SMT.showSExpr representation
    , "args = " ++ show (fmap unparseToString args)
    ]

parseNoJunkAxiom
    ::  ( Attribute.Axiom
        , Verified.SentenceAxiom
        )
    -> Maybe (Id, AST.UnresolvedSort)
parseNoJunkAxiom (attributes, SentenceAxiom {sentenceAxiomPattern})
  | Axiom.Constructor.isConstructor (Attribute.Axiom.constructor attributes)
  = parseNoJunkPattern sentenceAxiomPattern
  | otherwise = Nothing

parseNoJunkPattern
    :: TermLike Variable
    -> Maybe (Id , AST.UnresolvedSort)
parseNoJunkPattern patt = do  -- Maybe
    (name, sortBuilder, constructors) <- parseNoJunkPatternHelper patt
    -- We currently have invalid axioms like
    -- axiom{} \bottom{Sort'Hash'KVariable{}}() [constructor{}()] // no junk
    -- We could use them to prove anything we want and skip all the pain of
    -- doing actual proofs, but it seems that we should pretend that
    -- all is fine and look the other way when we encounter one of these
    -- inconsistent things.
    -- TODO (virgil): Transform this check into an assertion.
    when (null constructors) Nothing
    return (name, sortBuilder constructors)

parseNoJunkPatternHelper
    :: TermLike Variable
    ->  Maybe
        ( Id
        , [AST.UnresolvedConstructor] -> AST.UnresolvedSort
        , [AST.UnresolvedConstructor]
        )
parseNoJunkPatternHelper
    (Bottom_
        (SortActualSort SortActual
            { sortActualName, sortActualSorts = [] }
        )
    )
  = Just (sortActualName, fromConstructors, [])
  where
    encodedName = AST.encodable sortActualName
    fromConstructors :: [AST.UnresolvedConstructor] -> AST.UnresolvedSort
    fromConstructors constructors =
        AST.Sort
            { smtFromSortArgs =
                emptySortArgsToSmt (SMT.Atom $ AST.encode encodedName)
            , declaration = AST.SortDeclarationDataType
                SMT.DataTypeDeclaration
                    { name = encodedName
                    , typeArguments = []
                    , constructors = constructors
                    }
            }
parseNoJunkPatternHelper (Or_ _ first second) = do  -- Maybe
    (name, sortBuilder, constructors) <- parseNoJunkPatternHelper second
    constructor <- parseSMTConstructor first
    return (name, sortBuilder, constructor : constructors)
parseNoJunkPatternHelper _ = Nothing

parseSMTConstructor :: TermLike Variable -> Maybe AST.UnresolvedConstructor
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
        :: TermLike Variable
        -> (Set.Set (ElementVariable Variable), TermLike Variable)
    parseExists (Exists_ _ variable child) =
        (Set.insert variable childVars, unquantifiedPatt)
      where
        (childVars, unquantifiedPatt) = parseExists child
    parseExists unquantifiedPatt = (Set.empty, unquantifiedPatt)

    checkOnlyQuantifiedVariablesOnce
        :: Set.Set (ElementVariable Variable)
        -> [TermLike Variable]
        -> Maybe [ElementVariable Variable]
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        []
      | Set.null allowedVars = Just []
      | otherwise = Nothing
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        (patt0 : patts)
      = case patt0 of
        ElemVar_ var ->
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
        :: Symbol
        -> [ElementVariable Variable]
        -> Maybe AST.UnresolvedConstructor
    buildConstructor
        Symbol { symbolConstructor, symbolParams = [] }
        childVariables
      = do -- Maybe monad
        args <- zipWithM (parseVariableSort encodedName) [1..] childVariables
        return SMT.Constructor
            { name = AST.SymbolReference symbolConstructor
            , arguments = args
            }
      where
        encodedName = AST.encodable symbolConstructor

    -- TODO(virgil): Also handle parameterized sorts.
    buildConstructor _ _ = Nothing

    parseVariableSort
        :: AST.Encodable
        -> Integer
        -> ElementVariable Variable
        -> Maybe AST.UnresolvedConstructorArgument
    parseVariableSort
        constructorName
        index
        (ElementVariable Variable
            { variableSort =
                sort@(SortActualSort SortActual {sortActualSorts = []})
            }
        )
      = Just SMT.ConstructorArgument
            { name =
                AST.appendToEncoding
                    constructorName
                    ((Text.pack . show) index)
            , argType = AST.SortReference sort
            }
    parseVariableSort _ _ _ = Nothing
