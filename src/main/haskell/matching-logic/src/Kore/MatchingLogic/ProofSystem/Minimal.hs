{-|
Description: The minimal matching logic proof system

This module defines the minimal matching logic proof system,
which does not assume the existence of a definedness symbol.
 -}
module Kore.MatchingLogic.ProofSystem.Minimal where

import           Data.Text.Prettyprint.Doc       (Pretty (pretty))

import           Data.Functor.Foldable           (Fix (..))

import           Kore.MatchingLogic.AST          as AST
import           Kore.MatchingLogic.HilbertProof

{-|
  This type has constructors for each rule of the
  proof system.
  It is parameterized over the exact types of parts of patterns
  to allow working with different signatures or implementations.
  The 'term' parameter is used where the rule must be written
  with a literal pattern.
  'hypothesis' refers to hypotheses of a proof rule, it can be
  instantiated with names of the hypotheses or with the actual
  formulas giving the conclusions of those hypotheses.
 -}
data MLRule sort label var term hypothesis =
   Propositional1 term term
 | Propositional2 term term term
 | Propositional3 term term
 | ModusPonens hypothesis hypothesis
 | Generalization var hypothesis
 | VariableSubstitution var term var
 | ForallRule var term term
 | Framing label Int hypothesis
 | PropagateOr label Int term term
     -- ^ sigma(before ..,\phi1 \/ \phi2,.. after) <->
     --     sigma(before ..,\phi1, .. after) <-> sigma(before ..,\phi2,.. after)
 | PropagateExists label Int var term
     -- ^ sigma(before ..,Ex x. phi,.. after) <-> Ex x.sigma(before ..,phi,.. after)
 | Existence var
     -- ^ Ex x.x
 | Singvar var term [Int] [Int]
 deriving (Functor, Foldable, Traversable, Eq, Show)

transformRule :: (Applicative f)
              => (sort -> f sort')
              -> (label -> f label')
              -> (var -> f var')
              -> (term -> f term')
              -> (hyp -> f hyp')
              -> (MLRule sort label var term hyp
                  -> f (MLRule sort' label' var' term' hyp'))
transformRule sort label var term hypothesis rule = case rule of
    Propositional1 t1 t2 -> Propositional1 <$> term t1 <*> term t2
    Propositional2 t1 t2 t3 -> Propositional2 <$> term t1 <*> term t2 <*> term t3
    Propositional3 t1 t2 -> Propositional3 <$> term t1 <*> term t2
    ModusPonens h1 h2 -> ModusPonens <$> hypothesis h1 <*> hypothesis h2
    Generalization v h -> Generalization <$> var v <*> hypothesis h
    VariableSubstitution v1 t v2 ->
      VariableSubstitution <$> var v1
                           <*> term t
                           <*> var v2
    ForallRule v t1 t2 -> ForallRule <$> var v <*> term t1 <*> term t2
    Framing l pos h -> (flip Framing pos) <$> label l <*> hypothesis h
    PropagateOr l pos t1 t2
      -> (flip PropagateOr pos) <$> label l <*> term t1 <*> term t2
    PropagateExists l pos v t
      -> (flip PropagateExists pos) <$> label l <*> var v <*> term t
    Existence v -> Existence <$> var v
    Singvar v t path1 path2
      -> (\v' t' -> Singvar v' t' path1 path2) <$> var v <*> term t

-- | Lens focusing on the terms within a Rule.
ruleTerms :: (Applicative f)
          => (termA -> f termB)
          -> (MLRule sort label var termA hyp
              -> f (MLRule sort label var termB hyp))
ruleTerms f = transformRule pure pure pure f pure

-- | The 'MLRuleSig' synonym instantiates 'MLRule' to use
-- the sorts, labels, and patterns from the 'IsSignature' instance 'sig'
type MLRuleSig sig var = MLRule (Sort sig) (Label sig) var (WFPattern sig var)

-- | This instance is currently incomplete, it correctly checks
-- uses of propositional1 and propositional2 but rejects any other rules.
instance (IsSignature sig, Eq (Sort sig), Eq (Label sig), Eq var) =>
         ProofSystem (MLRuleSig sig var) (WFPattern sig var) where
  checkDerivation conclusion rule = case rule of
    Propositional1 phi1 phi2
      | wfPatSort phi1 == wfPatSort phi2
        -> let s = wfPatSort phi1
               phi1' = fromWFPattern phi1
               phi2' = fromWFPattern phi2
               statement = impliesP s phi1' (impliesP s phi2' phi1')
           in fromWFPattern conclusion == statement
    Propositional2 phi1 phi2 phi3
      | wfPatSort phi1 == wfPatSort phi2
      , wfPatSort phi1 == wfPatSort phi3
        -> let s = wfPatSort phi1
               phi1' = fromWFPattern phi1
               phi2' = fromWFPattern phi2
               phi3' = fromWFPattern phi3
               statement = impliesP s (impliesP s phi1' (impliesP s phi2' phi3'))
                               (impliesP s (impliesP s phi1' phi2') (impliesP s phi1' phi3'))
           in fromWFPattern conclusion == statement
    _ -> False
