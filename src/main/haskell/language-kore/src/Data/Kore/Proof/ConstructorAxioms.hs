{-|
Module      : Data.Kore.Proof.ConstructorAxioms
Description : No-junk, No-confusion etc. for non-AC constructors
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}



module Data.Kore.Proof.ConstructorAxioms where

import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Fix
import           Data.Fix
import           Data.Foldable
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools
import qualified Data.Map.Strict                       as M
import           Data.Maybe
import           Data.Reflection
import qualified Data.Set                              as S


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Util
import           Data.Kore.Proof.Dummy


import           Data.Hashable
import           GHC.Generics                          (Generic)

-- | Given head symbol h, return sort of h, arguments sorts s_i,
-- generates axiom of the form:
-- forall x_1 ... x_n , forall y_1 ... y_n
-- h(x_1, ..., x_n) = h(y_1, ..., y_n) ->
-- x_1 = y_1 /\ x_2 = y_2 /\ ... /\ x_n = y_n
-- where x_i, y_i : s_i
generateInjectivityAxiom
    :: Given (MetadataTools Object)
    => SymbolOrAlias Object 
    -> Sort Object
    -> [Sort Object]
    -> Term
generateInjectivityAxiom head resultSort childrenSorts =
    let vars name = 
            zipWith 
                (\n sort -> varS (name ++ show n) sort)
                [1..]
                childrenSorts
        xVars = vars "x"
        xVars' = map Var_ xVars
        yVars = vars "y"
        yVars' = map Var_ yVars
        fxEqfy = 
            mkApp head xVars'
            `mkEquals`
            mkApp head yVars'
        xsEqys = andN $ zipWith mkEquals xVars' yVars'
    in forallN xVars $ forallN yVars $ (fxEqfy `mkImplies` xsEqys)
