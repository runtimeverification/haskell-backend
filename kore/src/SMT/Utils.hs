module SMT.Utils (module SMT.Utils) where
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text, isPrefixOf, isSuffixOf)

import Prelude.Kore
import SMT qualified

splitAnd :: SMT.SExpr -> [SMT.SExpr]
splitAnd = \case
  SMT.List (SMT.Atom "and": xs) -> concatMap splitAnd xs
  other -> [other]

varAtoms :: SMT.SExpr -> Set Text
varAtoms = \case
  SMT.Atom a
    | "<" `isPrefixOf` a && ">" `isSuffixOf` a -> Set.singleton a
    | otherwise -> mempty
  SMT.List xs -> mconcat $ map varAtoms xs
  _ -> mempty

transitiveClosure :: Set SMT.SExpr ->  Set SMT.SExpr ->  Set SMT.SExpr
transitiveClosure cl' rest' = loop (Set.unions (Set.map varAtoms cl')) cl' rest'
  where
    loop clVars cl rest = 
      let (nonCommon, common) = Set.partition (null . Set.intersection clVars . varAtoms) rest in
        if null common then cl else 
          loop (clVars <> Set.unions (Set.map varAtoms common)) (cl <> common) nonCommon