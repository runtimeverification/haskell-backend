module Test.Kore.Equation.Common (
    Equation',
    concrete,
    symbolic,
    axiom,
    axiom_,
    functionAxiomUnification,
    functionAxiomUnification_,
    sortR,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Sup (
    Sup (..),
 )
import GHC.Natural (
    intToNatural,
 )
import Kore.Attribute.Axiom.Concrete (
    Concrete (..),
 )
import Kore.Attribute.Axiom.Symbolic (
    Symbolic (..),
 )
import Kore.Equation.Equation
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRuleVariable,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import Test.Kore.Internal.Predicate

type Equation' = Equation RewritingVariableName

axiom ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    Equation RewritingVariableName
axiom left right requires =
    (mkEquation left right){requires}

axiom_ ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName
axiom_ left right = axiom left right makeTruePredicate

functionAxiomUnification ::
    Symbol ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    Equation RewritingVariableName
functionAxiomUnification symbol args right requires =
    case args of
        [] -> (mkEquation (mkApplySymbol symbol []) right){requires}
        _ -> (mkEquation left right){requires, argument}
  where
    ~left = mkApplySymbol symbol variables
    sorts = fmap termLikeSort args
    ~variables = generateVariables (intToNatural (length args)) sorts
    generateVariables ~n sorts' =
        -- lazy argument to prevent arithmetic underflow
        fmap makeElementVariable (zip [0 .. n - 1] sorts')
    argument =
        Just $
            foldr1 makeAndPredicate $
                fmap (uncurry makeInPredicate) $
                    zip variables args
    makeElementVariable (num, sort) =
        mkElementVariable' (testId "funcVar") num sort
            & mkElemVar
    mkElementVariable' base counter variableSort =
        Variable
            { variableName =
                ElementVariableName $
                    mkRuleVariable $
                        VariableName{base, counter = Just (Element counter)}
            , variableSort
            }

functionAxiomUnification_ ::
    Symbol ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName
functionAxiomUnification_ symbol args right =
    functionAxiomUnification symbol args right makeTruePredicate

concrete ::
    [TermLike RewritingVariableName] ->
    Equation RewritingVariableName ->
    Equation RewritingVariableName
concrete vars =
    Lens.set
        (field @"attributes" . field @"concrete")
        (Concrete $ foldMap freeVariables vars)

symbolic ::
    [TermLike RewritingVariableName] ->
    Equation RewritingVariableName ->
    Equation RewritingVariableName
symbolic vars =
    Lens.set
        (field @"attributes" . field @"symbolic")
        (Symbolic $ foldMap freeVariables vars)

sortR :: Sort
sortR = mkSortVariable (testId "R")
