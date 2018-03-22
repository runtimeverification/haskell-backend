{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Data.Kore.Implicit.ImplicitVarsInternal
Description : Variable defimitions shared by modules defining kore.kore
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.Implicit.ImplicitVarsInternal where

import           Data.Kore.AST.Common
import           Data.Kore.MetaML.Builders

vf = unparameterizedVariable_ "#f"
vL = unparameterizedVariable_ "#L"
vphi = unparameterizedVariable_ "#phi"
vphi1 = unparameterizedVariable_ "#phi1"
vphi2 = unparameterizedVariable_ "#phi2"
vphi3 = unparameterizedVariable_ "#phi3"
vphii = unparameterizedVariable_ "#phii"
vpsi = unparameterizedVariable_ "#psi"
vR = unparameterizedVariable_ "#R"
vS = unparameterizedVariable_ "#S"
vS' = unparameterizedVariable_ "#S'"
vs = unparameterizedVariable_ "#s"
vs1 = unparameterizedVariable_ "#s1"
vs2 = unparameterizedVariable_ "#s2"
vs3 = unparameterizedVariable_ "#s3"
vs' = unparameterizedVariable_ "#s'"
vsigma = unparameterizedVariable_ "#sigma"
vu = unparameterizedVariable_ "#u"
v = unparameterizedVariable_ "#v"
v1 = unparameterizedVariable_ "#v1"
v2 = unparameterizedVariable_ "#v2"
vx = unparameterizedVariable_ "#x"
vx' = unparameterizedVariable_ "#x'"

pS = sortParameter "#sp"
spS = SortVariableSort pS
