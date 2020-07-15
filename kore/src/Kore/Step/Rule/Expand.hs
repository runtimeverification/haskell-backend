{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Expand
    ( ExpandSingleConstructors (..)
    ) where

import Prelude.Kore

import Control.Lens
    ( (%=)
    )
import qualified Control.Monad as Monad
import Control.Monad.State.Strict
    ( State
    , execState
    )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product
    ( field
    )
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC

import qualified Debug
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
import Kore.Internal.Predicate
    ( makeAndPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    , mkApplySymbol
    , mkElemVar
    )
import qualified Kore.Internal.TermLike as TermLike
    ( substitute
    )
import Kore.Sort
    ( Sort (..)
    , SortActual (SortActual)
    )
import qualified Kore.Sort as Sort.DoNotUse
import Kore.Step.RulePattern
    ( AllPathRule (..)
    , OnePathRule (..)
    , ReachabilityRule (..)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.RulePattern as RulePattern
import Kore.Syntax.Variable
import Kore.Variables.Fresh
    ( refreshVariable
    )
import qualified Pretty

-- | Instantiate variables on sorts with a single constructor
{- TODO(ttuegel): make this a strategy step, so that we expand any
    single-constructor variables at the start of each proof step.
    Going even further: make this a step in the variable simplifier?
-}
class ExpandSingleConstructors rule where
    expandSingleConstructors
        :: SmtMetadataTools attributes
        -> rule
        -> rule

instance ExpandSingleConstructors (RulePattern VariableName) where
    expandSingleConstructors
        metadataTools
        rule@(RulePattern _ _ _ _ _)
      = case rule of
        RulePattern
            {left, antiLeft, requires
            , rhs = RulePattern.RHS {existentials, right, ensures}
            } ->
            let leftVariables :: [ElementVariable VariableName]
                leftVariables =
                    mapMaybe retractElementVariable
                    $ FreeVariables.toList
                    $ freeVariables left
                allSomeVariables :: Set (SomeVariable VariableName)
                allSomeVariables =
                    FreeVariables.toSet (freeVariables rule)
                allElementVariables :: Set (ElementVariableName VariableName)
                allElementVariables =
                    Set.fromList
                    $ map variableName
                    $ mapMaybe retract (Set.toList allSomeVariables)
                        ++ existentials
                expansion
                    ::  Map.Map
                            (SomeVariable VariableName)
                            (TermLike VariableName)
                expansion =
                    expandVariables
                        metadataTools
                        leftVariables
                        allElementVariables
                substitutionPredicate =
                    ( Substitution.toPredicate
                    . Substitution.wrap
                    . Substitution.mkUnwrappedSubstitution
                    )
                        (Map.toList expansion)
                subst = Map.mapKeys variableName expansion
            in rule
                { RulePattern.left = TermLike.substitute subst left
                , RulePattern.antiLeft =
                    TermLike.substitute subst <$> antiLeft
                , RulePattern.requires =
                    makeAndPredicate
                        (Predicate.substitute subst requires)
                        substitutionPredicate
                , RulePattern.rhs = RulePattern.RHS
                    { existentials
                    , right = TermLike.substitute subst right
                    , ensures = Predicate.substitute subst ensures
                    }
                }

instance ExpandSingleConstructors OnePathRule where
    expandSingleConstructors tools =
        OnePathRule . expandSingleConstructors tools . getOnePathRule

instance ExpandSingleConstructors AllPathRule where
    expandSingleConstructors tools =
        AllPathRule . expandSingleConstructors tools . getAllPathRule

instance ExpandSingleConstructors ReachabilityRule where
    expandSingleConstructors tools (OnePath rule) =
        OnePath
        . OnePathRule
        . expandSingleConstructors tools
        . getOnePathRule
        $ rule
    expandSingleConstructors tools (AllPath rule) =
        AllPath
        . AllPathRule
        . expandSingleConstructors tools
        . getAllPathRule
        $ rule

data Expansion =
    Expansion
    { substitution :: !(Map (SomeVariable VariableName) (TermLike VariableName))
    , stale :: !(Set (ElementVariableName VariableName))
    }
    deriving (GHC.Generic)

type Expander = State Expansion

expandVariables
    :: SmtMetadataTools attributes
    -> [ElementVariable VariableName]
    -> Set (ElementVariableName VariableName)
    -> Map (SomeVariable VariableName) (TermLike VariableName)
expandVariables metadataTools variables stale =
    traverse expandAddVariable variables
    & flip execState Expansion { substitution = Map.empty, stale }
    & substitution
  where
    expandAddVariable :: ElementVariable VariableName -> Expander ()
    expandAddVariable variable = do
        term <- expandVariable metadataTools variable
        Monad.unless
            (mkElemVar variable == term)
            (field @"substitution" %= Map.insert (inject variable) term)

expandVariable
    :: SmtMetadataTools attributes
    -> ElementVariable VariableName
    -> Expander (TermLike VariableName)
expandVariable metadataTools variable@Variable { variableSort } = do
    expandSort metadataTools variable UseDirectly variableSort

expandSort
    :: SmtMetadataTools attributes
    -> ElementVariable VariableName
    -> VariableUsage
    -> Sort
    -> Expander (TermLike VariableName)
expandSort metadataTools defaultVariable variableUsage sort =
    case findSingleConstructor sort of
        Just constructor ->
            expandConstructor metadataTools defaultVariable constructor
        Nothing ->
            maybeNewVariable defaultVariable sort variableUsage
  where
    findSingleConstructor (SortVariableSort _) = Nothing
    findSingleConstructor (SortActualSort SortActual { sortActualName }) = do
        Attribute.Constructors.Constructors ctors <-
            findSortConstructors metadataTools sortActualName
        ctorLikes <- ctors
        case ctorLikes of
            Attribute.Constructors.ConstructorLikeConstructor ctor :| [] ->
                Just ctor
            _ -> Nothing

expandConstructor
    :: SmtMetadataTools attributes
    -> ElementVariable VariableName
    -> Attribute.Constructors.Constructor
    -> Expander (TermLike VariableName)
expandConstructor
    metadataTools
    defaultVariable
    Attribute.Constructors.Constructor { name = symbol, sorts }
  =
    mkApplySymbol symbol <$> traverse expandChildSort sorts
  where
    expandChildSort :: Sort -> Expander (TermLike VariableName)
    expandChildSort = expandSort metadataTools defaultVariable UseAsPrototype

{-| Context: we have a TermLike that contains a variables, and we
attempt to expand them into constructor applications whenever that's possible.

We expand a variable by attempting to expand its sort into an unique
constructor application, and, recursively, the argument sorts of that
constructor.

This data type tells us how to use the initial variable that we are expanding
when we can't expand a sort, so we have to return a variable of that sort
instead.
-}
data VariableUsage =
    UseDirectly
    -- ^ We don't need to generate a new variable, we are at the top and
    -- we didn't manage to expand anything, so we can just reuse the
    -- variable in the original term as the sort's expansion (useful if we
    -- want to have prettier terms).
  | UseAsPrototype
    -- ^ We have expanded the initial sort at least once, so we need a variable
    -- somewhere in the middle of the expansion. We can't reuse the original
    -- variable, so we need to generate a new one based on it.

maybeNewVariable
    :: HasCallStack
    => ElementVariable VariableName
    -> Sort
    -> VariableUsage
    -> Expander (TermLike VariableName)
maybeNewVariable
    variable@Variable { variableSort }
    sort
    UseDirectly
  =
    if sort /= variableSort
        then error "Unmatching sort for direct use variable."
        else pure (mkElemVar variable)
maybeNewVariable variable sort UseAsPrototype = do
    Expansion { stale } <- State.get
    case refreshVariable stale variable' of
        Just newVariable -> do
            field @"stale" %= Set.insert (variableName newVariable)
            pure (mkElemVar newVariable)
        Nothing ->
            (error . show . Pretty.hang 4 . Pretty.vsep)
                [ "Failed to generate a new name for:"
                , Pretty.indent 4 $ Debug.debug variable'
                , "while avoiding:"
                , Pretty.indent 4 $ Debug.debug stale
                ]
  where
    variable' = resort variable
    resort var = var { variableSort = sort }
