{- |
Module      : Kore.Rewrite.SMT.Representation.Sorts
Description : Builds an SMT representation for sorts.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Representation.Sorts (
    buildRepresentations,
    sortSmtFromSortArgs,
    emptySortArgsToSmt,
    applyToArgs,
) where

import Control.Monad (
    zipWithM,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Kore.Attribute.Hook (
    Hook (Hook),
 )
import Kore.Attribute.Hook qualified as Hook
import Kore.Attribute.Smtlib (
    applySExpr,
 )
import Kore.Attribute.Smtlib.Smtlib (
    Smtlib (Smtlib),
 )
import Kore.Attribute.Smtlib.Smtlib qualified as Smtlib
import Kore.Attribute.Sort qualified as Attribute (
    Sort,
 )
import Kore.Attribute.Sort qualified as Attribute.Sort
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors,
 )
import Kore.Attribute.Sort.Constructors qualified as Attribute.Constructors (
    Constructor (Constructor),
    ConstructorLike (ConstructorLikeConstructor),
    Constructors (getConstructors),
 )
import Kore.Attribute.Sort.Constructors qualified as Constructors.DoNotUse
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Int qualified as Int
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
    recursiveIndexedModuleSortDescriptions,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.SMT.AST qualified as AST
import Kore.Sort qualified as Kore
import Kore.Syntax.Sentence (
    SentenceSort (SentenceSort),
 )
import Kore.Syntax.Sentence qualified as SentenceSort (
    SentenceSort (..),
 )
import Kore.Unparser (
    unparseToString,
 )
import Kore.Verified qualified as Verified
import Prelude.Kore
import SMT qualified (
    Constructor (Constructor),
    ConstructorArgument (ConstructorArgument),
    DataTypeDeclaration (DataTypeDeclaration),
    SExpr (Atom, List),
    SortDeclaration (SortDeclaration),
    showSExpr,
    tBool,
    tInt,
 )
import SMT qualified as SMT.Constructor (
    Constructor (..),
 )
import SMT qualified as SMT.ConstructorArgument (
    ConstructorArgument (..),
 )
import SMT qualified as SMT.DataTypeDeclaration (
    DataTypeDeclaration (..),
 )
import SMT qualified as SMT.SortDeclaration (
    SortDeclaration (..),
 )

translateSort ::
    Map.Map Id AST.SmtSort ->
    Sort ->
    Maybe SMT.SExpr
translateSort
    sorts
    (SortActualSort SortActual{sortActualName, sortActualSorts}) =
        do
            AST.Sort{sortData} <- Map.lookup sortActualName sorts
            sortSmtFromSortArgs sortData sorts sortActualSorts
translateSort _ _ = Nothing

{- | Builds smt representations for sorts in the given module.

May ignore sorts that we don't handle yet (e.g. parameterized sorts).

All references to other sorts and symbols are left unresolved.
-}
buildRepresentations ::
    forall symbolAttribute.
    VerifiedModule symbolAttribute ->
    Map.Map Id Attribute.Constructors ->
    AST.UnresolvedDeclarations
buildRepresentations indexedModule sortConstructors =
    builtinAndSmtLibDeclarations
        `AST.mergePreferFirst` listToDeclarations
            (sortsWithConstructors builtinAndSmtLibSorts simpleSortIDs)
        `AST.mergePreferFirst` listToDeclarations simpleSortDeclarations
  where
    listToDeclarations ::
        [(Id, AST.UnresolvedSort)] -> AST.UnresolvedDeclarations
    listToDeclarations list =
        AST.Declarations
            { sorts = Map.fromList list
            , symbols = Map.empty
            }

    builtinAndSmtLibDeclarations :: AST.UnresolvedDeclarations
    builtinAndSmtLibDeclarations =
        listToDeclarations builtinSortDeclarations
            `AST.mergePreferFirst` listToDeclarations smtlibSortDeclarations

    builtinAndSmtLibSorts :: Set.Set Id
    builtinAndSmtLibSorts = Map.keysSet sorts
      where
        AST.Declarations{sorts} = builtinAndSmtLibDeclarations

    sortsWithConstructors ::
        Set.Set Id ->
        [Id] ->
        [(Id, AST.UnresolvedSort)]
    sortsWithConstructors blacklist whitelist =
        mapMaybe
            (sortWithConstructor sortConstructors)
            (filter (`Set.notMember` blacklist) whitelist)

    builtinSortDeclarations :: [(Id, AST.UnresolvedSort)]
    builtinSortDeclarations =
        extractDefinitionsFromSentences builtinSortDeclaration

    smtlibSortDeclarations :: [(Id, AST.UnresolvedSort)]
    smtlibSortDeclarations =
        extractDefinitionsFromSentences smtlibSortDeclaration

    simpleSortIDs :: [Id]
    simpleSortIDs = map fst simpleSortDeclarations

    simpleSortDeclarations :: [(Id, AST.UnresolvedSort)]
    simpleSortDeclarations =
        extractDefinitionsFromSentences simpleSortDeclaration

    extractDefinitionsFromSentences ::
        ( ( Attribute.Sort
          , Verified.SentenceSort
          ) ->
          Maybe (Id, AST.UnresolvedSort)
        ) ->
        [(Id, AST.UnresolvedSort)]
    extractDefinitionsFromSentences definitionExtractor =
        mapMaybe
            definitionExtractor
            (Map.elems $ recursiveIndexedModuleSortDescriptions indexedModule)

builtinSortDeclaration ::
    ( Attribute.Sort
    , Verified.SentenceSort
    ) ->
    Maybe (Id, AST.UnresolvedSort)
builtinSortDeclaration
    (attributes, SentenceSort{sentenceSortName}) =
        do
            smtRepresentation <- case getHook of
                Just name
                    | name == Int.sort -> return SMT.tInt
                    | name == Bool.sort -> return SMT.tBool
                _ -> Nothing
            return
                ( sentenceSortName
                , AST.Sort
                    { sortData = AST.EmptySortArgsToSmt smtRepresentation
                    , sortDeclaration =
                        AST.SortDeclaredIndirectly
                            (AST.AlreadyEncoded smtRepresentation)
                    }
                )
      where
        Hook{getHook} = Attribute.Sort.hook attributes

smtlibSortDeclaration ::
    ( Attribute.Sort
    , Verified.SentenceSort
    ) ->
    Maybe (Id, AST.UnresolvedSort)
smtlibSortDeclaration
    (attributes, SentenceSort{sentenceSortName}) =
        do
            smtRepresentation@(SMT.List (SMT.Atom smtName : sortArgs)) <- getSmtlib
            return
                ( sentenceSortName
                , AST.Sort
                    { sortData = AST.ApplyToArgs smtRepresentation
                    , sortDeclaration =
                        AST.SortDeclarationSort
                            SMT.SortDeclaration
                                { name = AST.AlreadyEncoded $ SMT.Atom smtName
                                , arity = length sortArgs
                                }
                    }
                )
      where
        Smtlib{getSmtlib} = Attribute.Sort.smtlib attributes

applyToArgs ::
    SMT.SExpr ->
    Map.Map Id AST.SmtSort ->
    [Sort] ->
    Maybe SMT.SExpr
applyToArgs sExpr definitions children = do
    children' <- mapM (translateSort definitions) children
    return $ applySExpr sExpr children'

simpleSortDeclaration ::
    ( Attribute.Sort
    , Verified.SentenceSort
    ) ->
    Maybe (Id, AST.UnresolvedSort)
simpleSortDeclaration
    ( _attribute
        , SentenceSort
            { sentenceSortName
            , sentenceSortParameters = []
            }
        ) =
        Just
            ( sentenceSortName
            , AST.Sort
                { sortData =
                    AST.EmptySortArgsToSmt (AST.encode encodedName)
                , sortDeclaration =
                    AST.SortDeclarationSort
                        SMT.SortDeclaration
                            { name = encodedName
                            , arity = 0
                            }
                }
            )
      where
        encodedName = AST.encodable sentenceSortName
simpleSortDeclaration _ = Nothing

sortSmtFromSortArgs :: AST.SortSExprFactory -> Map Kore.Id AST.SmtSort -> [Kore.Sort] -> Maybe SMT.SExpr
sortSmtFromSortArgs (AST.EmptySortArgsToSmt smtRepresentation) = emptySortArgsToSmt smtRepresentation
sortSmtFromSortArgs (AST.ApplyToArgs smtRepresentation) = applyToArgs smtRepresentation

emptySortArgsToSmt ::
    SMT.SExpr ->
    Map.Map Id AST.SmtSort ->
    [Sort] ->
    Maybe SMT.SExpr
emptySortArgsToSmt representation _ [] = Just representation
emptySortArgsToSmt representation _ args =
    (error . unlines)
        [ "Sorts with arguments not supported yet."
        , "representation=" ++ SMT.showSExpr representation
        , "args = " ++ show (fmap unparseToString args)
        ]

sortWithConstructor ::
    Map.Map Id Attribute.Constructors ->
    Id ->
    Maybe (Id, AST.UnresolvedSort)
sortWithConstructor sortConstructors sortId = do
    -- Maybe
    constructors <- Map.lookup sortId sortConstructors
    constructorLikeList <- Attribute.Constructors.getConstructors constructors
    constructorList <- traverse constructorFromLike constructorLikeList
    finalConstructors <- traverse buildConstructor (toList constructorList)
    return
        ( sortId
        , AST.Sort
            { sortData =
                AST.EmptySortArgsToSmt (AST.encode encodedName)
            , sortDeclaration =
                AST.SortDeclarationDataType
                    SMT.DataTypeDeclaration
                        { name = encodedName
                        , typeArguments = []
                        , constructors = finalConstructors
                        }
            }
        )
  where
    encodedName = AST.encodable sortId
    constructorFromLike
        (Attribute.Constructors.ConstructorLikeConstructor c) =
            Just c
    constructorFromLike _ = Nothing

buildConstructor ::
    Attribute.Constructors.Constructor ->
    Maybe AST.UnresolvedConstructor
buildConstructor
    Attribute.Constructors.Constructor
        { name = Symbol{symbolConstructor, symbolParams = []}
        , sorts
        } =
        do
            -- Maybe monad
            args <- zipWithM (buildConstructorArgument encodedName) [1 ..] sorts
            return
                SMT.Constructor
                    { name = AST.SymbolReference symbolConstructor
                    , arguments = args
                    }
      where
        encodedName = getId symbolConstructor
buildConstructor _ = Nothing

buildConstructorArgument ::
    Text.Text ->
    Integer ->
    Sort ->
    Maybe AST.UnresolvedConstructorArgument
buildConstructorArgument
    constructorName
    index
    sort@(SortActualSort SortActual{sortActualSorts = []}) =
        Just
            SMT.ConstructorArgument
                { name =
                    AST.Encodable $
                        SMT.Atom $
                            constructorName <> (Text.pack . show) index
                , argType = AST.SortReference sort
                }
buildConstructorArgument _ _ _ = Nothing
