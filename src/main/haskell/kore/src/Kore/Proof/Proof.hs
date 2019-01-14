{-|
Module      : Kore.Proof.Proof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unused-matches    #-}
{-# OPTIONS_GHC -Wno-name-shadowing    #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns  #-}

module Kore.Proof.Proof
  ( PropF(..)
  , Prop
  , Term
  , Var
  , Path
  , Proof
  , pattern By
  , useRule
  , interpretRule
  , impossible
  , LargeRule(..)
  , getConclusion
  , getJustification
  , getAssumptions
  , getFreeVars
  , assume
  , varS
  , symS
  )
where

import           Control.Lens
import           Data.Foldable
import           Data.Functor.Foldable
import           Data.Hashable
import           Data.Maybe
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc as P
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.ASTPrettyPrint
import qualified Kore.Domain.Builtin as Domain
import           Kore.Proof.Substitution
import           Kore.Unparser
import           Kore.Variables.Free

-- A note about partial pattern matches:
-- The basic Kore datatype has quite a few constructors,
-- and there are inevitably situations where we are only concerned
-- with 1 or 2 of them. For example, when alpha renaming we're only
-- interested in Forall_ and Exists_, when substituting we only deal
-- with Equals_ etc.
-- Sometimes these subsets of constructors could be factored out,
-- for example Forall_ and Exists_ could contain a Scope type
-- a la kmett's `bound`, then functions involving binders could
-- expect a Scope. Other times the situtation is just too particular.
-- In the end we decided that enforcing total pattern matches in
-- helper functions like alphaRename, provablySubstitute etc. is just too
-- much to ask. This is especially true since Kore theorems appear inside the
-- ByF constructor, so any tricks we use to encode subsets of constructors have
-- to be threaded through that type.
-- Hence most pattern matches end in `impossible`, which should be considered
-- a programmer error if it throws.

impossible :: a
impossible = error "The impossible happened."

type Term =
    PurePattern Object Domain.Builtin Variable (Valid (Variable Object) Object)
type Var = Variable Object

-- | Fix-able functor representing a single deduction step
-- `formula` is a matching logic formula, for now CommonPurePattern Object.
-- `rules` is a datatype encoding the valid deductions.
-- The rule type contains other subproofs as its children,
-- and should be `Functor`/`Traversable` over them.
-- Here we use a rule type `LargeRules` supporting natural deduction style
-- and the newer set of ML axioms.
-- `assumption` is the type of assumptions. This will normally be the same
-- as `formula`, except when converting to a line-based format, in which case
-- `assumption` and `subproof` can be a different type like `Int` representing a
-- pointer to a previous line.
data PropF formula rules assumption subproof
  = ByF
  { conclusion    :: formula
  , justification :: rules subproof
  , assumptions   :: S.Set assumption
  }
  deriving(Functor, Foldable, Traversable, Show, Generic)

type Prop formula rules = Fix (PropF formula rules formula)

pattern By
    :: formula
    -> rules (Fix (PropF formula rules assumption))
    -> S.Set assumption
    -> Fix (PropF formula rules assumption)
pattern By conclusion justification assumptions =
  Fix (ByF conclusion justification assumptions)

-- | Points to a location in a term at which a substitution
-- should be applied. For example, [1,0] points to the "b"
-- in "forall a. (b \/ a)". [] points to the top level, i.e.
-- the entire term.
-- Supplying an incorrect path should throw an error.
type Path = [Int]

-- | Proofs of object-level matching logic propositions, using the newer axioms.
-- In particular using types `Object`, `Variable`, `LargeRule`.
type Proof = Prop Term LargeRule

instance (Hashable formula, Hashable (rules subproof), Hashable assumption)
  => Hashable (PropF formula rules assumption subproof) where
  hashWithSalt s (ByF a b c) =
    s `hashWithSalt` a `hashWithSalt` b `hashWithSalt` S.toList c

data LargeRule subproof =
 -- | a |- a
   Assumption Term
 -- | From a |- b deduce |- a -> b
 | Discharge Term subproof
 -- | From |- A[x] deduce |- Forall x. A[x]
 | Abstract Var subproof
 -- | EVIL SHORTCUT! This bypasses the functionality check.
 -- Should move to using FunctionalSubst when you can.
 -- From |- forall x : s . A
 -- and any term (WHICH YOU SHOULD MAKE SURE IS FUNCTIONAL) phi : s
 -- deduce |- A[phi/x]
 | ForallElim Term subproof
 -- | From |- a , |- b deduce |- a /\ b
 | AndIntro subproof subproof
 -- | From |- a /\ b deduce |- a
 | AndElimL subproof
 -- | From |- a /\ b deduce |- b
 | AndElimR subproof
 -- | a |- a \/ b
 -- OrIntro a b
 | OrIntroL subproof Term
 -- | b |- a \/ b
 -- OrIntro a b
 | OrIntroR Term     subproof
 -- | OrElim (a \/ b) (C assuming a) (C assuming b)
 | OrElim subproof subproof subproof
 -- | |- T
 | TopIntro
 -- | From |- A[x] deduce |- (E x. A[x])
 | ExistsIntro Var Term subproof
 -- | ExistsElim (E x. p[x]) (C assuming p[y])
 | ExistsElim subproof Var Term subproof
 -- | From |- a, |- a -> b deduce |- b
 -- ModusPonens a b
 | ModusPonens subproof subproof
 -- (\forall x. phi) -> (\exists y. phi' = y) -> phi[phi'/x]
 -- FunctionalSubst x phi y phi'
 | FunctionalSubst Var Term Var Term
 -- | \exists y . x = y
 -- FunctionalVar x y
 | FunctionalVar Var Var
 -- | x = x
 -- EqualityIntro x
 | EqualityIntro Term
 -- | Path points to the _subtree_ of phi in which the substitution
 -- is to be applied at every possible point.
 -- This is technically less flexible than specifying every position of "x"
 -- But it's good enough for all practical purposes.
 -- phi_1 = phi_2 /\ phi[phi_1/x] -> phi[phi_2/x]
 -- EqualityElim phi_1 phi_2 phi [path]
 | EqualityElim Term Term Term Path
 -- | NOTE: Should probably rewrite axiom 8 to \forall x. x \in phi = \phi
 -- This should be exactly equivalent, and it fits the other axioms better.
 -- (\forall x . x \in phi) = phi
 | MembershipForall Var Term
 -- | x \in y = (x = y)
 | MembershipEq Var Var
 -- | x \in \not phi = \not (x \in phi)
 | MembershipNot Var Term
 -- | (x \in phi_1 /\ phi_2) = (x \in phi_1) /\ (x \in phi_2)
 | MembershipAnd Var Term Term
 -- | (x \in exists y . phi) = exists y . (x \in phi)
 | MembershipExists Var Var Term
 -- | x \in \sigma(phi_1,...,phi_i,...,phi_n)
 -- =
 -- \exists y . (y \in \phi_i /\ x \in \sigma(phi_1,...,y,...,phi_n))
 -- MembershipCong x y i (\sigma(...))
 | MembershipCong Var Var Int Term
 deriving(Show, Functor, Foldable, Generic, Traversable)


instance Hashable subproof => Hashable (LargeRule subproof)

instance Pretty a => Pretty (LargeRule a) where
    pretty e = sep $ case e of
        Assumption _
            -> ["Assumption"]
        Discharge a b
            -> ["Discharge", unparse a, pretty b]
        Abstract var a
            -> ["Abstract", unparse var, pretty a]
        ForallElim a b
            -> ["ForallElim", unparse a, pretty b]
        AndIntro a b
            -> ["AndIntro", pretty a, pretty b]
        AndElimR a
            -> ["AndElimR", pretty a]
        AndElimL a
            -> ["AndElimL", pretty a]
        OrIntroL a b
            -> ["OrIntroL", pretty a, unparse b]
        OrIntroR a b
            -> ["OrIntroR", unparse a, pretty b]
        OrElim a b c
            -> ["OrElim", pretty a, pretty b, pretty c]
        TopIntro
            -> ["TopIntro"]
        ExistsIntro var a b
            -> ["ExistsIntro", unparse var, unparse a, pretty b]
        ExistsElim a var b c
            -> ["ExistsElim", pretty a, unparse var, unparse b, pretty c]
        ModusPonens a b
            -> ["ModusPonens", pretty a, pretty b]
        FunctionalSubst var1 a var2 b
            -> ["FunctionalSubst", unparse var1, unparse a, unparse var2, unparse b]
        FunctionalVar var1 var2
            -> ["FunctionalVar", unparse var1, unparse var2]
        EqualityIntro a
            -> ["EqualityIntro", unparse a]
        EqualityElim a b c p
            -> ["EqualityElim", unparse a, unparse b, unparse c, pretty p]
        MembershipForall var a
            -> ["MembershipForall", unparse var, unparse a]
        MembershipEq var1 var2
            -> ["MembershipEq", unparse var1, unparse var2]
        MembershipNot var a
            -> ["MembershipNot", unparse var, unparse a]
        MembershipAnd var a b
            -> ["MembershipAnd", unparse var, unparse a, unparse b]
        MembershipExists var1 var2 a
            -> ["MembershipExists", unparse var1, unparse var2, unparse a]
        MembershipCong var1 var2 pos a
            -> ["MembershipCong", unparse var1, unparse var2, pretty pos, unparse a]

instance
  ( Unparse formula
  , Pretty (rules subproof)
  , Pretty subproof
  , Unparse assumption
  ) => Pretty (PropF formula rules assumption subproof) where
    pretty (ByF a b c) = "|- " <> unparse a <> P.line <> "By " <> pretty b

getConclusion
    :: Proof
    -> Term
getConclusion = conclusion . unfix

getJustification
    :: Proof
    -> LargeRule Proof
getJustification = justification . unfix

getAssumptions
    :: Proof
    -> S.Set  Term
getAssumptions = assumptions . unfix

-- | The set of all variables that appear free in the assumptions.
getFreeVars :: Proof -> S.Set Var
getFreeVars proof =
    S.unions
  $ map freePureVariables
  $ S.toList
  $ getAssumptions proof

-- | Shorthnad for `useRule . Assumption`
assume :: Term -> Proof
assume formula = By formula (Assumption formula) (S.singleton formula)

-- Given a Rule like `AndIntro a b`, useRule creates a proof, like
-- By (And a b) (AndIntro a b) (assumptions a `S.union` assumptions b)

-- There are two types of rules:
-- 1) "special" rules like Assumption, Discharge etc
-- These are natural deduction introduction/elimination rules which manipulate
-- quantifiers/assumptions in a tricky way.
-- 2) "mundane" rules like EqualityElim which merely
-- generate an axiom using a schema.
-- The "mundane" rules are passed off to "interpretRule"
-- which instantiates the schema.

useRule :: LargeRule Proof -> Proof
useRule (Assumption formula)
 = assume formula
useRule (Discharge hypothesis conclusion)
 = discharge hypothesis conclusion
    where
      discharge hypothesis prop@(By conclusion justification assumptions)
         = By
            (floorIfNotPredicate hypothesis `mkImplies` conclusion)
            (Discharge hypothesis prop)
            (S.delete hypothesis assumptions)
useRule (Abstract var conclusion)
 | elem var (getFreeVars conclusion) = abstract var conclusion
 | otherwise = error $ "Variable " ++ show var ++ " appears in assumptions."
    where
      abstract var prop@(By conclusion justification assumptions)
        | elem var $ getFreeVars prop
          = error $ "Variable "
                  ++ show var
                  ++ "appears in assumptions"
                  ++ show assumptions
        | otherwise
          = Fix $ (unfix prop) {
              conclusion = mkForall var conclusion
            }
useRule (ExistsElim producer var property (Fix consumer)) =
    case getConclusion producer of
      Exists_ _ v p
       | p == property -> Fix consumer
            { assumptions = S.delete property $ assumptions consumer
            }
       | otherwise -> error "The impossible happened."
      _ -> impossible
useRule rule@(OrElim disjunct left right)
  | getConclusion left == getConclusion right -- FIXME: too picky ==?
     = let Or_ _ leftAssumption rightAssumption = getConclusion disjunct
       in By
          (getConclusion left)
          rule
          (S.union
           (S.delete leftAssumption  $ getAssumptions left)
           (S.delete rightAssumption $ getAssumptions right)
          )
  | otherwise = impossible
useRule rule =
  By
  (interpretRule rule)
  rule
  (S.unions $ map getAssumptions $ toList rule)

-- | Given a rule such as `AndIntro a b`, converts it to the proposition
-- that it proves, such as "a /\ b".
interpretRule :: LargeRule Proof -> Term
interpretRule = \case
  ModusPonens a b ->
      let (Implies_ _ a' b') = getConclusion b
      in if a' == getConclusion a
        then b'
        else error
          $ "Can't match \n"
          ++ prettyPrintToString a'
          ++ "\n with \n"
          ++ prettyPrintToString (getConclusion a)
          ++ "in ModusPonens"
  FunctionalSubst x phi y phi' ->
      (mkForall x phi) `mkImplies` ((mkExists y (phi' `mkEquals_` mkVar y))
      `mkImplies`
      (subst (mkVar x) phi' phi))
  FunctionalVar x y ->
      mkExists y (mkVar x `mkEquals_` mkVar y)
  EqualityIntro a ->
      mkEquals_ a a
  EqualityElim phi1 phi2 phi path ->
        (phi1 `mkEquals_` phi2)
        `mkImplies` (
            phi
            `mkImplies`
            (localInPattern path (subst phi1 phi2) phi)
        )
  MembershipForall x phi ->
      (mkForall x (mkVar x `mkIn_` phi)) `mkEquals_` phi
  MembershipEq x y ->
      (mkVar x `mkIn_` mkVar y)
      `mkEquals_`
      (mkVar x `mkEquals_` mkVar y)
  MembershipAnd x phi1 phi2 ->
      (mkVar x `mkIn_` (phi1 `mkAnd` phi2))
      `mkEquals_`
      ((mkVar x `mkIn_` phi1) `mkAnd` (mkVar x `mkIn_` phi2))
  MembershipExists x y phi ->
      (mkVar x `mkIn_` (mkExists y phi))
      `mkEquals_`
      (mkExists y (mkVar x `mkIn_` phi))
  MembershipCong x y i phi ->
      (mkVar x `mkIn_` phi)
      `mkEquals_`
      (mkExists y $ (mkVar y `mkIn_` phi_i) `mkAnd` (mkVar x `mkIn_` phi'))
        where phi'       = phi & inPath [i] .~ (mkVar y)
              Just phi_i = phi ^? inPath [i]
  AndIntro a b ->
      mkAnd (getConclusion a) (getConclusion b)
  AndElimL a ->
      fromJust $ getConclusion a ^? inPath [0]
  AndElimR a ->
      fromJust $ getConclusion a ^? inPath [1]
  ExistsIntro var term property ->
      mkExists var $ subst (mkVar var) term $ getConclusion property
  OrIntroL a b ->
      mkOr (getConclusion a) b
  OrIntroR a b ->
      mkOr a (getConclusion b)
  ForallElim term proof ->
      case getConclusion proof of
          Forall_ s v p -> subst (mkVar v) term p
          _             -> impossible
  TopIntro ->
      mkTop_
  _ -> impossible

floorIfNotPredicate :: Term -> Term
floorIfNotPredicate p
 | isObviouslyPredicate p = p
 | otherwise = mkFloor_ p
