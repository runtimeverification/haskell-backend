module Test.Kore.Equation.Common
    ( Equation'
    , concrete
    , symbolic
    , axiom
    , axiom_
    , axiom'
    , axiom'_
    , functionAxiomUnification
    , functionAxiomUnification_
    , functionAxiomUnification'
    , functionAxiomUnification'_
    , sortR
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Product
    ( field
    )
import GHC.Natural
    ( intToNatural
    )

import Data.Sup
    ( Sup (..)
    )
import Kore.Attribute.Axiom.Concrete
    ( Concrete (..)
    )
import Kore.Attribute.Axiom.Symbolic
    ( Symbolic (..)
    )
import Kore.Equation.Equation
import Kore.Internal.TermLike

import qualified Kore.Equation.Equation as Equation
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkRuleVariable
    )
import Test.Kore
    ( testId
    )
import Test.Kore.Internal.Pattern
import Test.Kore.Internal.Predicate

type Equation' = Equation VariableName

axiom
    :: TestTerm
    -> TestTerm
    -> TestPredicate
    -> Equation'
axiom left right requires =
    (mkEquation left right) { requires }

axiom_
    :: TestTerm
    -> TestTerm
    -> Equation'
axiom_ left right = axiom left right makeTruePredicate

axiom'
    :: TestTerm
    -> TestTerm
    -> TestPredicate
    -> Equation RewritingVariableName
axiom' left right requires =
    axiom left right requires
    & Equation.mapVariables (pure mkRuleVariable)

axiom'_
    :: TestTerm
    -> TestTerm
    -> Equation RewritingVariableName
axiom'_ left right = axiom' left right makeTruePredicate

functionAxiomUnification
    :: Symbol
    -> [TestTerm]
    -> TestTerm
    -> TestPredicate
    -> Equation'
functionAxiomUnification symbol args right requires =
    case args of
        [] -> (mkEquation (mkApplySymbol symbol []) right) { requires }
        _  -> (mkEquation left right) { requires, argument }
  where
    left = mkApplySymbol symbol variables
    sorts = fmap termLikeSort args
    variables = generateVariables (intToNatural (length args)) sorts
    generateVariables n sorts' =
        fmap makeElementVariable (zip [0..n - 1] sorts')
    argument =
        Just
        $ foldr1 makeAndPredicate
        $ fmap (uncurry makeInPredicate)
        $ zip variables args
    makeElementVariable (num, sort) =
        mkElementVariable' (testId "funcVar") num sort
        & mkElemVar
    mkElementVariable' base counter variableSort =
        Variable
            { variableName =
                ElementVariableName
                    VariableName { base, counter = Just (Element counter) }
            , variableSort
            }

functionAxiomUnification_
    :: Symbol
    -> [TestTerm]
    -> TestTerm
    -> Equation'
functionAxiomUnification_ symbol args right =
    functionAxiomUnification symbol args right makeTruePredicate

functionAxiomUnification'
    :: Symbol
    -> [TestTerm]
    -> TestTerm
    -> TestPredicate
    -> Equation RewritingVariableName
functionAxiomUnification' symbol args right requires =
    functionAxiomUnification symbol args right requires
    & Equation.mapVariables (pure mkRuleVariable)

functionAxiomUnification'_
    :: Symbol
    -> [TestTerm]
    -> TestTerm
    -> Equation RewritingVariableName
functionAxiomUnification'_ symbol args right =
    functionAxiomUnification' symbol args right makeTruePredicate

-- TODO (Andrei): Fix this to `RewritingVariableName`
concrete
    :: InternalVariable variable
    => [TermLike variable]
    -> Equation variable
    -> Equation variable
concrete vars =
    Lens.set
        (field @"attributes" . field @"concrete")
        (Concrete $ foldMap freeVariables vars)

symbolic
    :: [TermLike RewritingVariableName]
    -> Equation RewritingVariableName
    -> Equation RewritingVariableName
symbolic vars =
    Lens.set
        (field @"attributes" . field @"symbolic")
        (Symbolic $ foldMap freeVariables vars)

sortR :: Sort
sortR = mkSortVariable (testId "R")
