{-|
Description: The minimal matching logic proof rules

This module defines the minimal matching logic proof rules,
which does not assume the existence of a definedness symbol.
-}
module Logic.Matching.Rules.Minimal where

import Control.Lens
import Data.Functor.Foldable
       ( Fix (..) )

import Kore.Error
import Logic.Matching.Error
import Logic.Matching.Pattern as Pattern
import Logic.Proof.Hilbert

newtype SubstitutedVariable var = SubstitutedVariable var
    deriving (Eq, Show)
newtype SubstitutingVariable var = SubstitutingVariable var
    deriving (Eq, Show)

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
data MLRule label var term hypothesis =
   Propositional1 term term
 | Propositional2 term term term
 | Propositional3 term term
 | ModusPonens hypothesis hypothesis
 | Generalization var hypothesis
 | VariableSubstitution
    (SubstitutedVariable var) term (SubstitutingVariable var)
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
              => (label -> f label')
              -> (var -> f var')
              -> (term -> f term')
              -> (hyp -> f hyp')
              -> (MLRule label var term hyp
                  -> f (MLRule label' var' term' hyp'))
transformRule label var term hypothesis rule = case rule of
    Propositional1 t1 t2 -> Propositional1 <$> term t1 <*> term t2
    Propositional2 t1 t2 t3 -> Propositional2 <$> term t1 <*> term t2 <*> term t3
    Propositional3 t1 t2 -> Propositional3 <$> term t1 <*> term t2
    ModusPonens h1 h2 -> ModusPonens <$> hypothesis h1 <*> hypothesis h2
    Generalization v h -> Generalization <$> var v <*> hypothesis h
    VariableSubstitution (SubstitutedVariable v1) t (SubstitutingVariable v2) ->
      VariableSubstitution <$> (SubstitutedVariable <$> var v1)
                           <*> term t
                           <*> (SubstitutingVariable <$> var v2)
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
          -> (MLRule label var termA hyp
              -> f (MLRule label var termB hyp))
ruleTerms f = transformRule pure pure f pure

-- | The 'MLRuleSig' synonym instantiates 'MLRule' to use
-- the sorts, labels, and patterns from the 'IsSignature' instance 'sig'
type MLRuleSig sig var {- hyp -}
    = MLRule (Label sig) var (WFPattern sig var) {- hyp -}

dummyFormulaVerifier :: formula -> Either (Error MLError) ()
dummyFormulaVerifier _ = return ()

-- Pattern.fromWFPattern
substVar :: (Eq sort, Eq var)
         => sort
         -> var
         -> var
         -> Pattern sort label var
         -> Maybe (Pattern sort label var)
substVar sort varFrom varTo = go
  where
    go pat@(Fix (Pattern.Exists _ sortBound varBound _))
      | (sortBound,varBound) == (sort,varFrom) = Just pat
      | (sortBound,varBound) == (sort,varTo) = Nothing
    go (Fix (Variable sortVar varVar))
      | (sortVar,varVar) == (sort,varFrom) = Just (Fix (Variable sort varTo))
    go (Fix pat) = Fix <$> traverse go pat

-- | This checks the minimal proof system over Kore.AST patterns.
instance (IsSignature sig, Eq (Sort sig), Eq (Label sig), Eq var) =>
         ProofSystem MLError (MLRuleSig sig var) (WFPattern sig var) where
  checkDerivation conclusion rule = case rule & ruleTerms %~ Just of
      Propositional1 a b ->
          expect $ a --> b --> a
      Propositional2 a b c ->
          expect $ (a --> b --> c) --> (a --> b) --> (a --> c)
      Propositional3 a b ->
          expect $ (notP' a --> notP' b) --> (b --> a)
      ModusPonens a (ImpliesP _ a' b) | a == a' ->
          expect $ Just b
      ModusPonens _ _ -> Left (Error [] "hypotheses have wrong form, modus ponens requires hypotheses of the form A->B and A")
      VariableSubstitution (SubstitutedVariable x) term (SubstitutingVariable y) ->
          case conclusion of
            ImpliesP _ (ForallP _ sVar var1 body) term2
              | Just body == term, var1 == x ->
                if Just (fromWFPattern term2)
                   == substVar sVar x y (fromWFPattern body) then
                  Right ()
                else
                  Left (Error [] "right hand term does not match phi[y/x]")
              | otherwise -> Left (Error [] "conclusion does not agree with arguments")
            _ -> Left (Error [] "malformed conclusion")
      ForallRule var term1 term2 ->
          case conclusion of
            ImpliesP _ (ForallP _ sVar var1 (ImpliesP _ p1 p2))
                       (ImpliesP _ p3 (ForallP _ sVar1 var2 p4))
              | var == var1, var1 == var2,
                sVar == sVar1, p1 == p3, p2 == p4,
                notFree sVar var1 p1 ->
                if term1 == Just p1 && term2 == Just p2
                then Right () else Left (Error [] "conclusion does not match rule arguments")
            _ -> Left (Error [] "conclusion not of right form")
      Generalization var hyp ->
          case conclusion of
            ForallP _ _sVar var1 body
              | var1 == var, hyp == body -> Right ()
            _ -> Left (Error [] "")
      Framing label pos (ImpliesP _ term1 term2) ->
          case conclusion of
              ImpliesP _ (ApplicationP label1 args1) (ApplicationP label2 args2)
                | label1 == label2,
                  (term1':_) <- drop pos args1,
                  (term2':_) <- drop pos args2  ->
                  if label == label1 && term1 == term1' && term2 == term2' then Right ()
                  else Left (Error [] "conclusion does not match rule arguments")
              _ -> Left (Error [] "conclusion has wrong form")
      Framing _ _ _ ->
          Left (Error [] "hypothesis has wrong form")

      -- PropagateOr:
      --   sigma(before ..,\phi1 \/ \phi2,.. after) <->
      --     sigma(before ..,\phi1, .. after) \/ sigma(before ..,\phi2,.. after)
      PropagateOr label pos phi1 phi2 -> do
          case conclusion of
            IffP _ (ApplicationP label1 args1)
                   (OrP _ (ApplicationP label2a args2a) (ApplicationP label2b args2b))
              | label == label1, label1 == label2a, label1 == label2b,
                (before1,OrP _ term1a term1b:after1) <- splitAt pos args1,
                (before2a,term2a:after2a) <- splitAt pos args2a,
                (before2b,term2b:after2b) <- splitAt pos args2b,
                before1 == before2a, before1 == before2b,
                after1 == after2a, after1 == after2b,
                term1a == term2a,
                term1b == term2b,
                phi1 == Just term1a, phi2 == Just term1b -> Right ()
            _ -> Left (Error [] "not proved")

      -- PropagateExists:
      --  sigma(before ..,Ex x. phi,.. after)
      --    <-> Ex x.sigma(before ..,phi,.. after)
      PropagateExists label pos var term ->
          case conclusion of
            IffP _ (ApplicationP label1 args1)
                   (ExistsP _ sVar2 var2 (ApplicationP label2 args2))
              | label == label1, label1 == label2,
                take pos args1 == take pos args2,
                drop (pos+1) args1 == drop (pos+1) args2,
                (ExistsP _ sVar1 var1 term1:_) <- drop pos args1,
                (term2:_) <- drop pos args2,
                sVar1 == sVar2, var1 == var2, term1 == term2,
                var == var1, Just term1 == term,
                all (notFree sVar1 var) (take pos args1++drop (pos+1) args1)
                  -> Right ()
            _ -> Left (Error [] "not proved")

      -- Existence:
      --  Ex x.x
      Existence var ->
          case conclusion of
            ExistsP _ sVar var1 (VariableP sVar' var2)
              | sVar == sVar', var1 == var2, var == var1 -> Right ()
            _ -> Left (Error [] "not exists")

      Singvar var termP path1 path2 ->
          case conclusion of
            NotP _ (AndP _ term1 term2) -> do
              occ1 <- followPath path1 term1
              occ2 <- followPath path2 term2
              case (occ1, occ2)  of
                (AndP _ (VariableP sVar1 var1) termPa,
                 AndP _ (VariableP sVar2 var2) (NotP _ termPb))
                      | var == var1, sVar1 == sVar2, var1 == var2,
                        termP == Just termPa, termPa == termPb -> Right ()
                _ -> Left (Error [] "subterms at given locations are not properly related")
            _ -> Left (Error [] "conclusion of singvar does not have expected forms")
    where
      -- | Local infix operator for building an implication
      infixr 1 -->
      (-->) :: Maybe (WFPattern sig var)
            -> Maybe (WFPattern sig var)
            -> Maybe (WFPattern sig var)
      (-->) = impliesP'
      expect (Just conclusion')
        | conclusion == conclusion' = Right ()
        | otherwise = Left (Error [] "incorrect conclusion")
      expect Nothing = Left (Error [] "incorrect arguments")
      followPath [] term = Right term
      followPath (position:path) (ApplicationP _ args)
        | (term':_) <- drop position args = followPath path term'
        | otherwise = Left (Error [] "Path contained position greater than number of children")
      followPath _ _ = Left (Error [] "Path attempted to enter non-application term")
