{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Expand
    ( expandOnePathSingleConstructors
    ) where

import Data.List
    ( foldl'
    , foldr
    )
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.Map as Map
import Data.Maybe
    ( mapMaybe
    )
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (getFreeVariables)
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute.Constructors
    ( Constructor (Constructor)
    , ConstructorLike (ConstructorLikeConstructor)
    , Constructors (Constructors)
    )
import qualified Kore.Attribute.Sort.Constructors as Constructors.DoNotUse
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    , findSortConstructors
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkApplySymbol
    , mkElemVar
    )
import qualified Kore.Internal.TermLike as TermLike
    ( freeVariables
    , substitute
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
    ( fromSubstitution
    , substitute
    )
import Kore.Sort
    ( Sort (..)
    , SortActual (SortActual)
    )
import qualified Kore.Sort as Sort.DoNotUse
import Kore.Step.Rule
    ( OnePathRule (OnePathRule)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , freeVariables
    )
import Kore.Syntax.ElementVariable
    ( ElementVariable (ElementVariable)
    )
import Kore.Syntax.Variable
    ( Variable (Variable, variableSort)
    )
import qualified Kore.Unification.Substitution as Substitution
    ( wrap
    )
import Kore.Variables.Fresh
    ( refreshVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (ElemVar)
    , extractElementVariable
    )

expandOnePathSingleConstructors
    :: SmtMetadataTools attributes
    -> OnePathRule Variable
    -> OnePathRule Variable
expandOnePathSingleConstructors metadataTools (OnePathRule rule) =
    OnePathRule (expandSingleConstructors metadataTools rule)

expandSingleConstructors
    :: SmtMetadataTools attributes
    -> RulePattern Variable
    -> RulePattern Variable
expandSingleConstructors
    metadataTools
    rule@(RulePattern _ _ _ _ _ _)
  = case rule of
    RulePattern {left, antiLeft, right, ensures, requires} ->
        let leftVariables :: [ElementVariable Variable]
            leftVariables =
                mapMaybe extractElementVariable
                $ Set.toList
                $ getFreeVariables
                $ TermLike.freeVariables left
            allUnifiedVariables :: Set.Set (UnifiedVariable Variable)
            allUnifiedVariables =
                getFreeVariables (RulePattern.freeVariables rule)
            allElementVariables :: Set.Set (ElementVariable Variable)
            allElementVariables = Set.fromList
                [ v | ElemVar v <- Set.toList allUnifiedVariables]
            expansion :: Map.Map (UnifiedVariable Variable) (TermLike Variable)
            expansion =
                expandVariables metadataTools leftVariables allElementVariables
            substitutionPredicate =
                Syntax.Predicate.fromSubstitution
                    (Substitution.wrap (Map.toList expansion))
        in rule
            { RulePattern.left = TermLike.substitute expansion left
            , RulePattern.antiLeft = TermLike.substitute expansion <$> antiLeft
            , RulePattern.right = TermLike.substitute expansion right
            , RulePattern.ensures =
                Syntax.Predicate.substitute expansion ensures
            , RulePattern.requires =
                makeAndPredicate
                    (Syntax.Predicate.substitute expansion requires)
                    substitutionPredicate
            }

expandVariables
    :: SmtMetadataTools attributes
    -> [ElementVariable Variable]
    -> Set.Set (ElementVariable Variable)
    -> Map.Map (UnifiedVariable Variable) (TermLike Variable)
expandVariables metadataTools variables toAvoid =
    fst $ foldl' expandAddVariable (Map.empty, toAvoid) variables
  where
    expandAddVariable
        ::  ( Map.Map (UnifiedVariable Variable) (TermLike Variable)
            , Set.Set (ElementVariable Variable)
            )
        -> ElementVariable Variable
        ->  ( Map.Map (UnifiedVariable Variable) (TermLike Variable)
            , Set.Set (ElementVariable Variable)
            )
    expandAddVariable (substitution, toAvoid') variable =
        case expandVariable metadataTools toAvoid' variable of
            (newVariables, term) ->
                ( if mkElemVar variable == term
                    then substitution
                    else Map.insert (ElemVar variable) term substitution
                , foldr Set.insert toAvoid' newVariables
                )

expandVariable
    :: SmtMetadataTools attributes
    -> Set.Set (ElementVariable Variable)
    -> ElementVariable Variable
    -> (Set.Set (ElementVariable Variable), TermLike Variable)
expandVariable
    metadataTools
    usedVariables
    variable@(ElementVariable Variable {variableSort})
  = expandSort metadataTools usedVariables variable UseDirectly variableSort

expandSort
    :: SmtMetadataTools attributes
    -> Set.Set (ElementVariable Variable)
    -> ElementVariable Variable
    -> VariableUsage
    -> Sort
    -> (Set.Set (ElementVariable Variable), TermLike Variable)
expandSort
    _metadataTools
    usedVariables
    defaultVariable
    variableUsage
    sort@(SortVariableSort _)
  =
    (updatedUsedVariables, variable)
  where
    (updatedUsedVariables, variable) =
        maybeNewVariable usedVariables defaultVariable sort variableUsage
expandSort
    metadataTools
    usedVariables
    defaultVariable
    variableUsage
    sort@(SortActualSort SortActual { sortActualName })
  =
    case findSortConstructors metadataTools sortActualName of
        Just
            (Attribute.Constructors.Constructors
                (Just
                    ( Attribute.Constructors.ConstructorLikeConstructor
                        constructor
                    :| []
                    )
                )
            ) ->
                expandConstructor
                    metadataTools
                    usedVariables
                    defaultVariable
                    constructor
        _ -> maybeNewVariable usedVariables defaultVariable sort variableUsage

expandConstructor
    :: SmtMetadataTools attributes
    -> Set.Set (ElementVariable Variable)
    -> ElementVariable Variable
    -> Attribute.Constructors.Constructor
    -> (Set.Set (ElementVariable Variable), TermLike Variable)
expandConstructor
    metadataTools
    usedVariables
    defaultVariable
    Attribute.Constructors.Constructor { name = symbol, sorts }
  = (finalUsedVariables, mkApplySymbol symbol children)
  where
    (children, finalUsedVariables) =
        foldr expandChildSort ([], usedVariables) sorts

    expandChildSort
        :: Sort
        -> ([TermLike Variable], Set.Set (ElementVariable Variable))
        -> ([TermLike Variable], Set.Set (ElementVariable Variable))
    expandChildSort sort (terms, beforeUsedVariables) =
        (term : terms, afterUsedVariables)
      where
        (afterUsedVariables, term) =
            expandSort
                metadataTools
                beforeUsedVariables
                defaultVariable
                UseAsPrototype
                sort

data VariableUsage = UseDirectly | UseAsPrototype

maybeNewVariable
    :: Set.Set (ElementVariable Variable)
    -> ElementVariable Variable
    -> Sort
    -> VariableUsage
    -> (Set.Set (ElementVariable Variable), TermLike Variable)
maybeNewVariable
    usedVariables
    variable@(ElementVariable Variable {variableSort})
    sort
    UseDirectly
  =
    if sort /= variableSort
        then error "Unmatching sort for direct use variable."
        else (usedVariables, mkElemVar variable)
maybeNewVariable usedVariables variable sort UseAsPrototype =
    case refreshVariable usedVariables (resort variable) of
        Just newVariable ->
            ( Set.insert newVariable usedVariables
            , mkElemVar newVariable
            )
        Nothing ->
            (error . unlines)
                [ "Expecting a variable refresh for"
                , show variable
                , "but got nothing. Used variables:"
                , show usedVariables
                ]
  where
    resort (ElementVariable var) = ElementVariable var { variableSort = sort }
