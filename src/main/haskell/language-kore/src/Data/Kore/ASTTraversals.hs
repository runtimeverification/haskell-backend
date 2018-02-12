{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( visit
                               , freeVariables
                               , freeVarsVisitor
                               ) where

import           Data.Typeable (Typeable)

import           Data.Kore.AST

{-|'visit' is the specialization of a catamorphism for patterns.
It takes as argument a local visitor/reduce function which reduces to a result
parameterized patterns containing in any pattern position the result of
visiting that pattern.
-}
visit
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var result -> result)
    -> fixedPoint
    -> result
visit phi = self
  where
    self = unFixPattern (phi . fmap self)

freeVariables :: UnifiedPattern -> [UnifiedVariable Variable]
freeVariables = visit freeVarsVisitor

freeVarsVisitor
    :: (Typeable var, IsMeta a, Show (var Object), Show (var Meta),
        Eq (UnifiedVariable var))
    => Pattern a var [UnifiedVariable var] -> [UnifiedVariable var]
freeVarsVisitor (VariablePattern v) = [asUnifiedVariable v]
freeVarsVisitor (ExistsPattern e) =
    filter (/= existsVariable e) (existsPattern e)
freeVarsVisitor (ForallPattern f) =
    filter (/= forallVariable f) (forallPattern f)
freeVarsVisitor p                  = foldMap id p --default rule

substitute :: UnifiedPattern -> [(UnifiedVariable Variable, UnifiedPattern)] -> UnifiedPattern
substitute = foldr substituteOne
  where substituteOne s = fst . visit (substituteVisitor s)

substituteVisitor
    :: IsMeta a
    => (UnifiedVariable Variable, UnifiedPattern)
    -> Pattern a Variable (UnifiedPattern, UnifiedPattern)
    -> (UnifiedPattern, UnifiedPattern)
substituteVisitor (uv, up) (VariablePattern v)
    | uv == asUnifiedVariable v = (up, unified)
    | otherwise = (unified, unified)
  where unified = asUnifiedPattern (VariablePattern v)
substituteVisitor (uv, _) ep@(ExistsPattern e)
    | uv == existsVariable e =
        let origPattern = asUnifiedPattern $ fmap snd ep
        in (origPattern, origPattern)
substituteVisitor (uv, _) fp@(ForallPattern e)
    | uv == forallVariable e =
        let origPattern = asUnifiedPattern $ fmap snd fp
        in (origPattern, origPattern)
substituteVisitor _ p =
    (asUnifiedPattern $ fmap fst p, asUnifiedPattern $ fmap snd p)
