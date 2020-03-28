{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Equation
    ( Equation (..)
    , mkEquation
    , mapVariables
    , refreshVariables
    , checkInstantiation, InstantiationFailure (..)
    , isSimplificationRule
    , equationPriority
    , matchEquation, MatchEquationError (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Axiom.Constructor
    ( Constructor (..)
    )
import Kore.Attribute.Functional
    ( Functional (..)
    )
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Subsort
    ( Subsorts (..)
    )
import Kore.Internal.Predicate
    ( NotPredicate
    , Predicate
    , makePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , InternalVariable
    , SetVariable
    , TermLike
    , Variable
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Step
    ( Renaming
    )
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Variables.Fresh as Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

data Equation variable = Equation
    { requires :: !(Predicate variable)
    , left  :: !(TermLike variable)
    , right :: !(TermLike variable)
    , ensures :: !(Predicate variable)
    , attributes :: !(Attribute.Axiom Symbol variable)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

-- | Creates a basic, unconstrained, Equality pattern
mkEquation
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Equation variable
mkEquation left right =
    assert (TermLike.termLikeSort left == TermLike.termLikeSort right)
    Equation
        { left
        , requires = Predicate.makeTruePredicate sort
        , right
        , ensures = Predicate.makeTruePredicate sort
        , attributes = Default.def
        }
  where
    sort = TermLike.termLikeSort left

instance NFData variable => NFData (Equation variable)

instance SOP.Generic (Equation variable)

instance SOP.HasDatatypeInfo (Equation variable)

instance Debug variable => Debug (Equation variable)

instance (Debug variable, Diff variable) => Diff (Equation variable)

instance InternalVariable variable => Pretty (Equation variable) where
    pretty equation@(Equation _ _ _ _ _) =
        Pretty.vsep
            [ "requires:"
            , Pretty.indent 4 (unparse requires)
            , "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        Equation
            { requires
            , left
            , right
            , ensures
            } = equation

instance TopBottom (Equation variable) where
    isTop _ = False
    isBottom _ = False

instance SQL.Table (Equation Variable)

instance SQL.Column (Equation Variable) where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

instance
    InternalVariable variable
    => From (Equation variable) (TermLike variable)
  where
    from equation
      -- \ceil axiom
      | isTop requires
      , isTop ensures
      , TermLike.Ceil_ _ sort1 _ <- left
      , TermLike.Top_ sort2 <- right
      , sort1 == sort2
      = left

      -- unconditional equation
      | isTop requires
      , isTop ensures
      = TermLike.mkEquals_ left right

      -- conditional equation
      | otherwise =
        TermLike.mkImplies
            (from @(Predicate variable) requires)
            (TermLike.mkAnd
                (TermLike.mkEquals_ left right)
                (from @(Predicate variable) ensures)
            )
      where
        Equation { left, requires, right, ensures } = equation

instance
    InternalVariable variable
    => HasFreeVariables (Equation variable) variable
  where
    freeVariables rule@(Equation _ _ _ _ _) = case rule of
        Equation { left, requires, right, ensures } ->
            freeVariables left
            <> freeVariables requires
            <> freeVariables right
            <> freeVariables ensures

mapVariables
    :: (Ord variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> Equation variable1 -> Equation variable2
mapVariables mapElemVar mapSetVar equation@(Equation _ _ _ _ _) =
    equation
        { requires = mapPredicateVariables requires
        , left = mapTermLikeVariables left
        , right = mapTermLikeVariables right
        , ensures = mapPredicateVariables ensures
        , attributes =
            Attribute.mapAxiomVariables mapElemVar mapSetVar attributes
        }
  where
    Equation { requires, left, right, ensures, attributes } = equation
    mapTermLikeVariables = TermLike.mapVariables mapElemVar mapSetVar
    mapPredicateVariables = Predicate.mapVariables mapElemVar mapSetVar

refreshVariables
    :: InternalVariable variable
    => FreeVariables variable
    -> Equation variable
    -> (Renaming variable, Equation variable)
refreshVariables
    (FreeVariables.getFreeVariables -> avoid)
    equation@(Equation _ _ _ _ _)
  =
    let rename = Fresh.refreshVariables avoid originalFreeVariables
        mapElemVars elemVar =
            case Map.lookup (ElemVar elemVar) rename of
                Just (ElemVar elemVar') -> elemVar'
                _ -> elemVar
        mapSetVars setVar =
            case Map.lookup (SetVar setVar) rename of
                Just (SetVar setVar') -> setVar'
                _ -> setVar
        subst = TermLike.mkVar <$> rename
        left' = TermLike.substitute subst left
        requires' = Predicate.substitute subst requires
        right' = TermLike.substitute subst right
        ensures' = Predicate.substitute subst ensures
        attributes' =
            Attribute.mapAxiomVariables mapElemVars mapSetVars attributes
        equation' =
            equation
                { left = left'
                , requires = requires'
                , right = right'
                , ensures = ensures'
                , attributes = attributes'
                }
    in (rename, equation')
  where
    Equation { left, requires, right, ensures, attributes } = equation
    originalFreeVariables =
        FreeVariables.getFreeVariables $ freeVariables equation

{- | @InstantiationFailure@ represents a reason to reject the instantiation of
an 'Equation'.
 -}
data InstantiationFailure variable
    = NotConcrete (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a symbolic term where a concrete
    -- term was required.
    | NotSymbolic (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a concrete term where a symbolic
    -- term was required.
    | NotInstantiated (UnifiedVariable variable)
    -- ^ The variable was not instantiated.

checkInstantiation
    :: InternalVariable variable
    => Equation variable
    -> Map (UnifiedVariable variable) (TermLike variable)
    -> [InstantiationFailure variable]
checkInstantiation rule substitutionMap =
    notConcretes <> notSymbolics
  where
    attrs = attributes rule
    concretes = FreeVariables.getFreeVariables
        . Attribute.unConcrete . Attribute.concrete $ attrs
    symbolics = FreeVariables.getFreeVariables
        . Attribute.unSymbolic . Attribute.symbolic $ attrs
    checkConcrete var =
        case Map.lookup var substitutionMap of
            Nothing -> Just (NotInstantiated var)
            Just termLike
              | TermLike.isConstructorLike termLike -> Nothing
              | otherwise -> Just (NotConcrete var termLike)
    checkSymbolic var =
        case Map.lookup var substitutionMap of
            Nothing -> Just (NotInstantiated var)
            Just termLike
              | TermLike.isConstructorLike termLike ->
                Just (NotSymbolic var termLike)
              | otherwise -> Nothing
    notConcretes = mapMaybe checkConcrete (Set.toList concretes)
    notSymbolics = mapMaybe checkSymbolic (Set.toList symbolics)

isSimplificationRule :: Equation variable -> Bool
isSimplificationRule Equation { attributes } =
    isSimplification
  where
    Attribute.Simplification { isSimplification } =
        Attribute.simplification attributes

equationPriority :: Equation variable -> Integer
equationPriority = Attribute.getPriorityOfAxiom . attributes

data MatchEquationError variable
    = NotEquation !(TermLike variable)
    | RequiresError !(NotPredicate variable)
    | EnsuresError !(NotPredicate variable)
    | FunctionalAxiom
    | ConstructorAxiom
    | SubsortAxiom

{- | Match a term encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'TermLike' does
not encode a normal rewrite or function axiom.
-}
matchEquation
    :: forall variable
    .  InternalVariable variable
    => Attribute.Axiom Symbol variable
    -> TermLike variable
    -> Either (MatchEquationError variable) (Equation variable)
matchEquation attributes termLike
  | isFunctionalAxiom = Left FunctionalAxiom
  | isConstructorAxiom = Left ConstructorAxiom
  | isSubsortAxiom = Left SubsortAxiom
  | TermLike.Forall_ _ _ child <- termLike = matchEquation attributes child
  | otherwise = match termLike >>= removeRedundantEnsures
  where
    isFunctionalAxiom = (isDeclaredFunctional . Attribute.functional) attributes
    isConstructorAxiom = (isConstructor . Attribute.constructor) attributes
    isSubsortAxiom = (not . null . getSubsorts . Attribute.subsorts) attributes
    match
        (TermLike.Implies_ _
            requires
            (TermLike.And_ _
                (TermLike.Equals_ _ _ left right)
                ensures
            )
        )
      = do
        requires' <- makePredicate requires & Bifunctor.first RequiresError
        ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
        pure Equation
            { requires = requires'
            , left
            , right
            , ensures = ensures'
            , attributes
            }

    match (TermLike.Equals_ _ sort left right) =
        pure Equation
            { requires = Predicate.makeTruePredicate sort
            , left
            , right
            , ensures = Predicate.makeTruePredicate sort
            , attributes
            }

    match left@(TermLike.Ceil_ _ sort _) =
        pure Equation
            { requires = Predicate.makeTruePredicate sort
            , left
            , right = TermLike.mkTop sort
            , ensures = Predicate.makeTruePredicate sort
            , attributes
            }

    match termLike' = Left (NotEquation termLike')

    -- If the ensures and requires are the same, then the ensures is redundant.
    removeRedundantEnsures equation@Equation { requires, ensures }
      | ensures == requires =
        return equation { ensures = Predicate.makeTruePredicate sort }
      | otherwise = return equation
      where
        sort = termLikeSort (Predicate.unwrapPredicate ensures)
