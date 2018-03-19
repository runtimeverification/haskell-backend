{-|
Module      : Data.Kore.Implicit.ImplicitKore
Description : Builds the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.ImplicitKoreImpl where

import           Data.Kore.AST.Common
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders
import           Data.Kore.Variables.Free  (freeVariables)

import           Data.Fix
import           Data.Foldable             (foldl')
import qualified Data.Map                  as Map
import qualified Data.Set                  as Set


{-|'equalsSortParam' is the sort param implicitly used for 'equals' when no
other sort can be inferred.
-}
equalsSortParam :: SortVariable Meta
equalsSortParam = sortParameter "#esp"

equalsSort :: Sort Meta
equalsSort = SortVariableSort equalsSortParam

{-|'withSort' transforms an 'UnsortedPatternStub' in a 'SortedPatternStub'.
-}
withSort :: Sort Meta -> MetaPatternStub -> MetaPatternStub
withSort s (UnsortedPatternStub p) =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = p s
        , sortedPatternSort = s
        }
withSort
    s
    p@(SortedPatternStub SortedPattern { sortedPatternSort = existingSort })
  =
    if s == existingSort
        then p
        else
            error
                (  "Unmatched sorts: "
                ++ show s
                ++ " and "
                ++ show existingSort
                ++ "."
                )

{-|'parameterizedAxiom' creates an axiom that has sort parameters from
a pattern.
-}
parameterizedAxiom :: [SortVariable Meta] -> MetaPatternStub -> MetaSentenceAxiom
parameterizedAxiom _ (UnsortedPatternStub p) =
    error ("Cannot infer sort for " ++ show (p dummyMetaSort) ++ ".")
parameterizedAxiom
    parameters
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = s }
    )
  =
    SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = quantifyFreeVariables s (Fix p)
        , sentenceAxiomAttributes = MetaAttributes []
        }

{-|'parameterizedEqualsAxiom' is a special case for a 'parameterizedAxiom' that
contains an equals pattern.
-}
parameterizedEqualsAxiom
    :: [SortVariable Meta] -> MetaPatternStub -> MetaPatternStub -> MetaSentenceAxiom
parameterizedEqualsAxiom parameters first second =
    parameterizedAxiom
        (equalsSortParam : parameters)
        (withSort equalsSort (equals_ first second))

{-|'equalsAxiom' is a special case for an axiom that contains an equals pattern.
-}
equalsAxiom :: MetaPatternStub -> MetaPatternStub -> MetaSentenceAxiom
equalsAxiom = parameterizedEqualsAxiom []

{-|'quantifyFreeVariables' quantifies all free variables in the given pattern.
It assumes that the pattern has the provided sort.
-}
-- TODO(virgil): Make this generic and move it in ASTHelpers.hs
quantifyFreeVariables
    :: Sort Meta -> CommonMetaPattern -> CommonMetaPattern
quantifyFreeVariables s p =
    foldl'
        (wrapAndQuantify s)
        p
        (checkUnique (freeVariables p))

wrapAndQuantify
    :: Sort Meta
    -> CommonMetaPattern
    -> Variable Meta
    -> CommonMetaPattern
wrapAndQuantify s p var =
    Fix
        (ForallPattern Forall
            { forallSort = s
            , forallVariable = var
            , forallChild = p
            }
        )

checkUnique
    :: Set.Set (Variable Meta) -> Set.Set (Variable Meta)
checkUnique variables =
    case checkUniqueEither (Set.toList variables) Map.empty of
        Right _  -> variables
        Left err -> error err

checkUniqueEither
    :: [Variable Meta]
    -> Map.Map String (Variable Meta)
    -> Either String ()
checkUniqueEither [] _ = Right ()
checkUniqueEither (var:vars) indexed =
    case Map.lookup name indexed of
        Nothing -> checkUniqueEither vars (Map.insert name var indexed)
        Just existingV ->
            Left
                (  "Conflicting variables: "
                ++ show var
                ++ " and "
                ++ show existingV
                ++ "."
                )
  where
    name = getId (variableName var)

