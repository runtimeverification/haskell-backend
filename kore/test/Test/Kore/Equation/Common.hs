module Test.Kore.Equation.Common
    ( Equation'
    , concrete
    , symbolic
    , axiom
    , axiom_
    , functionAxiomUnification
    , functionAxiomUnification_
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
    (mkEquation sortR left right) { requires }

axiom_
    :: TestTerm
    -> TestTerm
    -> Equation'
axiom_ left right = axiom left right (makeTruePredicate sortR)

functionAxiomUnification
    :: Symbol
    -> [TestTerm]
    -> TestTerm
    -> TestPredicate
    -> Equation'
functionAxiomUnification symbol args right requires =
    case args of
        [] -> (mkEquation sortR (mkApplySymbol symbol []) right) { requires }
        _  -> (mkEquation sortR left right) { requires, argument }
  where
    left = mkApplySymbol symbol variables
    sorts = fmap termLikeSort args
    variables = generateVariables (intToNatural (length args)) sorts
    generateVariables n sorts' =
        fmap makeElementVariable (zip [0..n - 1] sorts')
    argument =
        Just
        $ foldr1 makeAndPredicate
        $ fmap (uncurry (makeInPredicate sortR))
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
    functionAxiomUnification symbol args right (makeTruePredicate sortR)

concrete :: [TestTerm] -> Equation' -> Equation'
concrete vars =
    Lens.set
        (field @"attributes" . field @"concrete")
        (Concrete $ foldMap freeVariables vars)

symbolic :: [TestTerm] -> Equation' -> Equation'
symbolic vars =
    Lens.set
        (field @"attributes" . field @"symbolic")
        (Symbolic $ foldMap freeVariables vars)

sortR :: Sort
sortR = mkSortVariable (testId "R")
