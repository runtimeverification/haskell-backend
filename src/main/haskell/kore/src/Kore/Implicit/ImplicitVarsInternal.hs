{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Kore.Implicit.ImplicitVarsInternal
Description : Variable defimitions shared by modules defining kore.kore
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Implicit.ImplicitVarsInternal where

import Kore.AST.Builders
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( CommonPurePatternStub )
import Kore.MetaML.AST

vf, vL, vphi, vphi1, vphi2, vphi3, vphii, vpsi, vR, vS, vS', vs, vs1, vs2, vs3
    , vs', vsigma, vu, v1, v2, vx, vx' :: MetaPatternStub

implicitUnparameterizedVariable :: String -> CommonPurePatternStub level
implicitUnparameterizedVariable name =
    unparameterizedVariable_ name AstLocationImplicit

vf = implicitUnparameterizedVariable "#f"
vL = implicitUnparameterizedVariable "#L"
vphi = implicitUnparameterizedVariable "#phi"
vphi1 = implicitUnparameterizedVariable "#phi1"
vphi2 = implicitUnparameterizedVariable "#phi2"
vphi3 = implicitUnparameterizedVariable "#phi3"
vphii = implicitUnparameterizedVariable "#phii"
vpsi = implicitUnparameterizedVariable "#psi"
vR = implicitUnparameterizedVariable "#R"
vS = implicitUnparameterizedVariable "#S"
vS' = implicitUnparameterizedVariable "#S'"
vs = implicitUnparameterizedVariable "#s"
vs1 = implicitUnparameterizedVariable "#s1"
vs2 = implicitUnparameterizedVariable "#s2"
vs3 = implicitUnparameterizedVariable "#s3"
vs' = implicitUnparameterizedVariable "#s'"
vsigma = implicitUnparameterizedVariable "#sigma"
vu = implicitUnparameterizedVariable "#u"
v = implicitUnparameterizedVariable "#v"
v1 = implicitUnparameterizedVariable "#v1"
v2 = implicitUnparameterizedVariable "#v2"
vx = implicitUnparameterizedVariable "#x"
vx' = implicitUnparameterizedVariable "#x'"

pS = sortParameter Meta "#sp" AstLocationImplicit
spS = SortVariableSort pS
