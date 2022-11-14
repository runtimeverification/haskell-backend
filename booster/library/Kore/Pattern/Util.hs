{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Util (
    sortOfTerm,
) where

import Kore.Pattern.Base

-- | Returns the sort of a term
sortOfTerm :: Term -> Sort
sortOfTerm (AndTerm sort _ _) = sort
sortOfTerm (SymbolApplication sort _ _ _) = sort
sortOfTerm (DomainValue sort _) = sort
sortOfTerm (Var Variable{variableSort}) = variableSort
