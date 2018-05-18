{-|
Module      : Data.Kore.Implicit.ImplicitKoreImpl
Description : Helpers for building the implicit kore definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.ImplicitKoreImpl where

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.MetaML.AST

import           Data.Fix
import           Data.Foldable              (foldl')
import qualified Data.Map                   as Map
import           Data.Proxy
import qualified Data.Set                   as Set


{-|'equalsSortParam' is the sort param implicitly used for 'equals' when no
other sort can be inferred. This parameter is assumed not to be used in
any pattern, except for top-level pattern of an axiom. Using it will have
unpredictable effects.
-}
equalsSortParam :: SortVariable Meta
equalsSortParam = sortParameter Meta "#esp" AstLocationImplicit

equalsSort :: Sort Meta
equalsSort = SortVariableSort equalsSortParam

{-|'parameterizedAxiom' creates an axiom that has sort parameters from
a pattern.
-}
parameterizedAxiom
    :: [SortVariable Meta] -> MetaPatternStub -> MetaSentenceAxiom
parameterizedAxiom _ (UnsortedPatternStub p) =
    error ("Cannot infer sort for " ++ show (p (dummySort (Proxy :: Proxy Meta))) ++ ".")
parameterizedAxiom
    parameters
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = s }
    )
  =
    SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = quantifyFreeVariables s (Fix p)
        , sentenceAxiomAttributes = Attributes []
        }

{-|'parameterizedEqualsAxiom' is a special case for a 'parameterizedAxiom' that
contains an equals pattern.
Note that 'equalsSortParam' AKA @#esp@ is assumed not to be used in any of
the patterns. Using it will have unpredictable effects.
-}
parameterizedEqualsAxiom
    :: [SortVariable Meta]
    -> MetaPatternStub
    -> MetaPatternStub
    -> MetaSentenceAxiom
parameterizedEqualsAxiom parameters first second =
    parameterizedAxiom
        (equalsSortParam : parameters)
        (withSort equalsSort (equals_ first second))

{-|'equalsAxiom' is a special case for an axiom that contains an equals pattern.
Note that 'equalsSortParam' AKA @#esp@ is assumed not to be used in any of
the patterns. Using it will have unpredictable effects.
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
        (checkUnique (metaFreeVariables p))

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

