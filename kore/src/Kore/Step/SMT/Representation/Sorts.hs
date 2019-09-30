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

import Control.Monad
    ( zipWithM
    )
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( mapMaybe
    )
import qualified Data.Set as Set
import qualified Data.Text as Text

import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import Kore.Attribute.Hook
    ( Hook (Hook)
    )
import qualified Kore.Attribute.Hook as Hook
import Kore.Attribute.Smtlib
    ( applySExpr
    )
import Kore.Attribute.Smtlib.Smtlib
    ( Smtlib (Smtlib)
    )
import qualified Kore.Attribute.Smtlib.Smtlib as Smtlib
import qualified Kore.Attribute.Sort as Attribute
    ( Sort
    )
import qualified Kore.Attribute.Sort as Attribute.Sort
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute.Constructors
    ( Constructor (Constructor)
    , ConstructorLike (ConstructorLikeConstructor)
    , Constructors (getConstructors)
    )
import qualified Kore.Attribute.Sort.Constructors as Constructors.DoNotUse
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Int as Int
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , recursiveIndexedModuleSortDescriptions
    )
import Kore.Internal.TermLike
import Kore.Sort
    ( Sort (SortActualSort)
    , SortActual (SortActual)
    )
import qualified Kore.Sort as SortActual
    ( SortActual (..)
    )
import qualified Kore.Step.SMT.AST as AST
import Kore.Syntax.Id
    ( Id
    )
import Kore.Syntax.Sentence
    ( SentenceSort (SentenceSort)
    )
import qualified Kore.Syntax.Sentence as SentenceSort
    ( SentenceSort (..)
    )
import Kore.Unparser
    ( unparseToString
    )
import qualified Kore.Verified as Verified
import qualified SMT
    ( Constructor (Constructor)
    , ConstructorArgument (ConstructorArgument)
    , DataTypeDeclaration (DataTypeDeclaration)
    , SExpr (Atom, List)
    , SortDeclaration (SortDeclaration)
    , nameFromSExpr
    , showSExpr
    , tBool
    , tInt
    )
import qualified SMT as SMT.DataTypeDeclaration
    ( DataTypeDeclaration (..)
    )
import qualified SMT as SMT.SortDeclaration
    ( SortDeclaration (..)
    )
import qualified SMT as SMT.ConstructorArgument
    ( ConstructorArgument (..)
    )
import qualified SMT as SMT.Constructor
    ( Constructor (..)
    )


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
    -> Map.Map Id Attribute.Constructors
    -> AST.UnresolvedDeclarations
buildRepresentations indexedModule sortConstructors =
    builtinAndSmtLibDeclarations
    `AST.mergePreferFirst`
        listToDeclarations
            (sortsWithConstructors builtinAndSmtLibSorts simpleSortIDs)
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

    sortsWithConstructors
        :: Set.Set Id
        -> [Id]
        -> [(Id, AST.UnresolvedSort)]
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

sortWithConstructor
    :: Map.Map Id Attribute.Constructors
    -> Id
    -> Maybe (Id, AST.UnresolvedSort)
sortWithConstructor sortConstructors sortId = do  -- Maybe
    constructors <- Map.lookup sortId sortConstructors
    constructorLikeList <- Attribute.Constructors.getConstructors constructors
    constructorList <- traverse constructorFromLike constructorLikeList
    finalConstructors <-
        traverse buildConstructor (Foldable.toList constructorList)
    return
        ( sortId
        , AST.Sort
            { smtFromSortArgs =
                emptySortArgsToSmt (SMT.Atom $ AST.encode encodedName)
            , declaration = AST.SortDeclarationDataType
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
        (Attribute.Constructors.ConstructorLikeConstructor c)
      = Just c
    constructorFromLike _ = Nothing

buildConstructor
    :: Attribute.Constructors.Constructor
    -> Maybe AST.UnresolvedConstructor
buildConstructor
    Attribute.Constructors.Constructor
        { name = Symbol { symbolConstructor, symbolParams = [] }
        , sorts
        }
  = do  -- Maybe monad
    args <- zipWithM (buildConstructorArgument encodedName) [1..] sorts
    return SMT.Constructor
        { name = AST.SymbolReference symbolConstructor
        , arguments = args
        }
  where
    encodedName = AST.encodable symbolConstructor
buildConstructor _ = Nothing

buildConstructorArgument
    :: AST.Encodable
    -> Integer
    -> Sort
    -> Maybe AST.UnresolvedConstructorArgument
buildConstructorArgument
    constructorName
    index
    sort@(SortActualSort SortActual {sortActualSorts = []})
    = Just SMT.ConstructorArgument
        { name =
            AST.appendToEncoding
                constructorName
                ((Text.pack . show) index)
        , argType = AST.SortReference sort
        }
buildConstructorArgument _ _ _ = Nothing
