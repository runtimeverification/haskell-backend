module SMT.Utils (module SMT.Utils) where
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import Prelude.Kore
import SMT qualified

atoms :: SMT.SExpr -> Set Text
atoms = \case
  SMT.Atom a -> Set.singleton a
  SMT.List xs -> mconcat $ map atoms xs
  _ -> mempty

transitiveClosure :: Set SMT.SExpr ->  Set SMT.SExpr ->  Set SMT.SExpr
transitiveClosure cl' rest' = loop (Set.unions (Set.map atoms cl')) cl' rest'
  where
    loop clAtoms cl rest = 
      let (nonCommon, common) = Set.partition (null . Set.intersection clAtoms . atoms) rest in
        if null common then cl else 
          loop (clAtoms <> Set.unions (Set.map atoms common)) (cl <> common) nonCommon