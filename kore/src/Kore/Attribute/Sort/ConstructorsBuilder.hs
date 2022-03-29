{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Attribute.Sort.ConstructorsBuilder (
    indexBySort,
) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Kore.Attribute.Axiom qualified as Attribute (
    Axiom,
 )
import Kore.Attribute.Axiom qualified as Attribute.Axiom (
    constructor,
 )
import Kore.Attribute.Axiom.Constructor qualified as Axiom.Constructor
import Kore.Attribute.Sort.Constructors (
    Constructor (Constructor),
    ConstructorLike (..),
    Constructors (Constructors),
 )
import Kore.Attribute.Sort.Constructors qualified as Constructors.DoNotUse
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
    recursiveIndexedModuleAxioms,
 )
import Kore.Internal.Symbol (
    Symbol (Symbol),
 )
import Kore.Internal.Symbol qualified as Symbol.DoNotUse
import Kore.Internal.TermLike (
    TermLike,
    pattern App_,
    pattern Bottom_,
    pattern ElemVar_,
    pattern Exists_,
    pattern Or_,
 )
import Kore.Sort (
    Sort (SortActualSort),
    SortActual (SortActual),
 )
import Kore.Sort qualified as Sort.DoNotUse
import Kore.Syntax.Id (
    Id,
 )
import Kore.Syntax.Sentence (
    SentenceAxiom (SentenceAxiom),
 )
import Kore.Syntax.Sentence qualified as Sentence.DoNotUse
import Kore.Syntax.Variable
import Kore.Verified qualified as Verified (
    SentenceAxiom,
 )
import Prelude.Kore

indexBySort ::
    VerifiedModule symbolAttribute ->
    Map.Map Id Constructors
indexBySort indexedModule =
    Map.fromList
        ( mapMaybe
            parseNoJunkAxiom
            (recursiveIndexedModuleAxioms indexedModule)
        )

parseNoJunkAxiom ::
    ( Attribute.Axiom Symbol variable
    , Verified.SentenceAxiom
    ) ->
    Maybe (Id, Constructors)
parseNoJunkAxiom (attributes, SentenceAxiom{sentenceAxiomPattern})
    | Axiom.Constructor.isConstructor (Attribute.Axiom.constructor attributes) =
        parseNoJunkPattern sentenceAxiomPattern
    | otherwise = Nothing

parseNoJunkPattern ::
    TermLike VariableName ->
    Maybe (Id, Constructors)
parseNoJunkPattern patt = do
    -- Maybe
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

parseNoJunkPatternHelper ::
    TermLike VariableName ->
    Maybe
        ( Id
        , [ConstructorLike] -> Constructors
        , [ConstructorLike]
        )
parseNoJunkPatternHelper
    ( Bottom_
            ( SortActualSort
                    SortActual
                        { sortActualName
                        , sortActualSorts = []
                        }
                )
        ) =
        Just (sortActualName, fromConstructors, [])
      where
        -- TODO: Delete?
        fromConstructors :: [ConstructorLike] -> Constructors
        fromConstructors [] = Constructors Nothing
        fromConstructors (constructor : constructors) =
            Constructors (Just (constructor :| constructors))
parseNoJunkPatternHelper (Or_ _ first second) = do
    -- Maybe
    (name, sortBuilder, constructors) <- parseNoJunkPatternHelper second
    constructor <- parseSMTConstructor first
    return (name, sortBuilder, constructor : constructors)
parseNoJunkPatternHelper _ = Nothing

parseSMTConstructor :: TermLike VariableName -> Maybe ConstructorLike
parseSMTConstructor patt =
    case parsedPatt of
        App_ symbol children -> do
            childVariables <-
                checkOnlyQuantifiedVariablesOnce quantifiedVariables children
            buildConstructor symbol childVariables
        _ -> Nothing
  where
    (quantifiedVariables, parsedPatt) = parseExists patt

    parseExists ::
        TermLike VariableName ->
        (Set.Set (ElementVariable VariableName), TermLike VariableName)
    parseExists (Exists_ _ variable child) =
        (Set.insert variable childVars, unquantifiedPatt)
      where
        (childVars, unquantifiedPatt) = parseExists child
    parseExists unquantifiedPatt = (Set.empty, unquantifiedPatt)

    checkOnlyQuantifiedVariablesOnce ::
        Set.Set (ElementVariable VariableName) ->
        [TermLike VariableName] ->
        Maybe [ElementVariable VariableName]
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        []
            | Set.null allowedVars = Just []
            | otherwise = Nothing
    checkOnlyQuantifiedVariablesOnce
        allowedVars
        (patt0 : patts) =
            case patt0 of
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

    buildConstructor ::
        Symbol ->
        [ElementVariable VariableName] ->
        Maybe ConstructorLike
    buildConstructor
        symbol@Symbol{symbolParams = []}
        childVariables =
            do
                -- Maybe monad
                sorts <- traverse parseVariableSort childVariables
                return
                    ( ConstructorLikeConstructor
                        Constructor
                            { name = symbol
                            , sorts
                            }
                    )

    -- TODO(virgil): Also handle parameterized constructors and inj.
    buildConstructor _ _ = Nothing

    parseVariableSort ::
        ElementVariable VariableName ->
        Maybe Sort
    parseVariableSort
        Variable
            { variableSort =
                sort@(SortActualSort SortActual{sortActualSorts = []})
            } =
            Just sort
    -- TODO(virgil): Also handle parameterized sorts.
    parseVariableSort _ = Nothing
