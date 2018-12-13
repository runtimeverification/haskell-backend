{-|
Module      : Kore.Proof.ConstructorAxioms
Description : No-junk, No-confusion etc. for non-AC constructors
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Proof.ConstructorAxioms
    ( generateInjectivityAxiom
    , generateNoConfusionAxiom
    , generateCoveringAxiom
    ) where

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Proof.Proof
import Kore.Proof.Util

-- | Given head symbol h, return sort of h, arguments sorts s_i,
-- generates axiom of the form:
-- forall x_1 ... x_n , forall y_1 ... y_n
-- h(x_1, ..., x_n) = h(y_1, ..., y_n) ->
-- x_1 = y_1 /\ x_2 = y_2 /\ ... /\ x_n = y_n
-- where x_i, y_i : s_i
generateInjectivityAxiom
    :: SymbolOrAlias Object
    -> Sort Object
    -> [Sort Object]
    -> Term
generateInjectivityAxiom head' resultSort childrenSorts =
    let (xVars, xVars') = generateVarList childrenSorts "x"
        (yVars, yVars') = generateVarList childrenSorts "y"
        fxEqfy =
            mkEquals_
                (mkApp resultSort head' xVars')
                (mkApp resultSort head' yVars')
        xsEqys = mkAndN $ zipWith mkEquals_ xVars' yVars'
    in mkForallN xVars $ mkForallN yVars $ (fxEqfy `mkImplies` xsEqys)

-- | No confusion: two different constructors cannot generate the same term.
-- `not (f(x_1,...,x_n) = g(y_1,...,y_m))`
generateNoConfusionAxiom
    :: Sort Object
    -> SymbolOrAlias Object
    -> [Sort Object]
    -> Sort Object
    -> SymbolOrAlias Object
    -> [Sort Object]
    -> Term
generateNoConfusionAxiom s1 h1 c1 s2 h2 c2 =
    let (_, xVars') = generateVarList c1 "x"
        (_, yVars') = generateVarList c2 "y"
    in mkNot $ mkEquals_
         (mkApp s1 h1 xVars')
         (mkApp s2 h2 yVars')

generateCoveringAxiom
    :: Sort Object
    -> [(SymbolOrAlias Object, [Sort Object])]
    -> Term
generateCoveringAxiom sort cons =
    mkForall v $ mkOrN $ map itIsThisConstructor cons
      where
        v = varS "v" sort
        itIsThisConstructor (h, cs) =
            mkExistsN vars
          $ mkVar v `mkEquals_` mkApp sort h vars'
          where
            (vars, vars') = generateVarList cs "x"
