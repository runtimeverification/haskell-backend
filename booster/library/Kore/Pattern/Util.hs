{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Util (
    sortOfTerm,
    sortOfTermOrPredicate,
    retractPattern,
) where

import Kore.Pattern.Base

-- | Returns the sort of a term
sortOfTerm :: Term -> Sort
sortOfTerm (AndTerm sort _ _) = sort
sortOfTerm (SymbolApplication sort _ _ _) = sort
sortOfTerm (DomainValue sort _) = sort
sortOfTerm (Var Variable{variableSort}) = variableSort

sortOfTermOrPredicate :: TermOrPredicate -> Maybe Sort
sortOfTermOrPredicate (TermAndPredicate Pattern{term}) = Just (sortOfTerm term)
sortOfTermOrPredicate (APredicate _) = Nothing

retractPattern :: TermOrPredicate -> Maybe Pattern
retractPattern (TermAndPredicate patt) = Just patt
retractPattern _ = Nothing
