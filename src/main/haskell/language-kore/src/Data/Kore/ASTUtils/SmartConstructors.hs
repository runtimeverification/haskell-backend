{-|
Module      : Data.Kore.ASTUtils.SmartConstructors
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Data.Kore.ASTUtils.SmartConstructors
( -- * Utility funcs for dealing with sorts
  getSort
, forceSort
, flexibleSort
, isRigid
, isFlexible
, makeSortsAgree
, ensureSortAgreement
-- * Lenses -- all applicative
, patternLens
, inputSort   -- | will have 0 or 1 inhabitants
, resultSort  -- | will have 0 or 1 inhabitants
, variable    -- | will have 0 or 1 inhabitants
, allChildren -- | will have 0+ inhabitants
, inPath
, localInPattern
-- * Pattern synonyms
, pattern And_
, pattern App_
, pattern Bottom_
, pattern Ceil_
, pattern DV_
, pattern Equals_
, pattern Exists_
, pattern Floor_
, pattern Forall_
, pattern Iff_
, pattern Implies_
, pattern In_
, pattern Next_
, pattern Not_
, pattern Or_
, pattern Rewrites_
, pattern Top_
, pattern Var_
, pattern V
, pattern StringLiteral_
, pattern CharLiteral_
, mkAnd
, mkApp
, mkBottom
, mkCeil
, mkDomainValue
, mkEquals
, mkExists
, mkFloor
, mkForall
, mkIff
, mkImplies
, mkIn
, mkNext
, mkNot
, mkOr
, mkRewrites
, mkTop
, mkVar
, mkStringLiteral
, mkCharLiteral
, mkSort
)
where


import           Control.Lens
import           Control.Monad.State

import           Data.Fix
import           Data.Foldable
import           Data.Reflection


import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML                  (PureMLPattern)
import           Data.Kore.IndexedModule.MetadataTools


-- | Gets the sort of of a pattern, taking the Metadatatools implicitly
-- from the context.
-- The smart constructors `mkAnd`, etc also require this context.
-- Usage: give metadatatools (... computation with Given Metadatatools ..)
getSort
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => PureMLPattern level var
    -> Sort level
getSort x = getPatternResultSort (getResultSort given) $ unFix x

-- | Placeholder sort for when we construct a new predicate
-- But we don't know yet where it's going to be attached.
-- No particular way to avoid this, unfortunately.
-- This will probably happen often during proof routines.
flexibleSort
    :: MetaOrObject level
    => Sort level
flexibleSort =
    SortVariableSort $ SortVariable
        { getSortVariable = noLocationId "*" } --FIXME

pattern And_
    :: Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern App_
    :: SymbolOrAlias level
    -> [PureMLPattern level var]
    -> PureMLPattern level var

pattern Bottom_
    :: Sort level
    -> PureMLPattern level var

pattern Ceil_
    :: Sort level
    -> Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern DV_
  :: Sort Object
  -> PureMLPattern Object var
  -> PureMLPattern Object var

pattern Equals_
    :: Sort level
    -> Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Exists_
    :: Sort level
    -> var level
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Floor_
    :: Sort level
    -> Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Forall_
    :: Sort level
    -> var level
    -> PureMLPattern level var
    -> PureMLPattern level var
pattern Iff_
    :: Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Implies_
    :: Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern In_
    :: Sort level
    -> Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Next_
  :: Sort Object
  -> PureMLPattern Object var
  -> PureMLPattern Object var

pattern Not_
    :: Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Or_
    :: Sort level
    -> PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var

pattern Rewrites_
  :: Sort Object
  -> PureMLPattern Object var
  -> PureMLPattern Object var
  -> PureMLPattern Object var

pattern Top_
    :: Sort level
    -> PureMLPattern level var

pattern Var_
    :: var level
    -> PureMLPattern level var

pattern StringLiteral_
  :: StringLiteral
  -> PureMLPattern Meta var

pattern CharLiteral_
  :: CharLiteral
  -> PureMLPattern Meta var

-- No way to make multiline pragma?
-- NOTE: If you add a case to the AST type, add another synonym here.
{-# COMPLETE And_, App_, Bottom_, Ceil_, DV_, Equals_, Exists_, Floor_, Forall_, Iff_, Implies_, In_, Next_, Not_, Or_, Rewrites_, Top_, Var_, StringLiteral_, CharLiteral_ #-}

pattern And_          s2   a b = Fix (AndPattern (And s2 a b))
pattern App_ h c               = Fix (ApplicationPattern (Application h c))
pattern Bottom_       s2       = Fix (BottomPattern (Bottom s2))
pattern Ceil_      s1 s2   a   = Fix (CeilPattern (Ceil s1 s2 a))
pattern DV_           s2   a   = Fix (DomainValuePattern (DomainValue s2 a))
pattern Equals_    s1 s2   a b = Fix (EqualsPattern (Equals s1 s2 a b))
pattern Exists_       s2 v a   = Fix (ExistsPattern (Exists s2 v a))
pattern Floor_     s1 s2   a   = Fix (FloorPattern (Floor s1 s2 a))
pattern Forall_       s2 v a   = Fix (ForallPattern (Forall s2 v a))
pattern Iff_          s2   a b = Fix (IffPattern (Iff s2 a b))
pattern Implies_      s2   a b = Fix (ImpliesPattern (Implies s2 a b))
pattern In_        s1 s2   a b = Fix (InPattern (In s1 s2 a b))
pattern Next_         s2   a   = Fix (NextPattern (Next s2 a))
pattern Not_          s2   a   = Fix (NotPattern (Not s2 a))
pattern Or_           s2   a b = Fix (OrPattern (Or s2 a b))
pattern Rewrites_     s2   a b = Fix (RewritesPattern (Rewrites s2 a b))
pattern Top_          s2       = Fix (TopPattern (Top s2))
pattern Var_             v     = Fix (VariablePattern v)

pattern V :: var level -> PureMLPattern level var
pattern V x = Var_ x

pattern StringLiteral_ s = Fix (StringLiteralPattern s)
pattern CharLiteral_   c = Fix (CharLiteralPattern   c)

patternLens
    :: (Applicative f, MetaOrObject level)
    => (Sort level -> f (Sort level))
    -> (Sort level -> f (Sort level))
    -> (var level -> f (var level))
    -> (PureMLPattern level var -> f (PureMLPattern level var))
    -> (PureMLPattern level var -> f (PureMLPattern level var))
patternLens
  i   -- input sort
  o   -- result sort
  var -- variable
  c   -- child
  = \case
  And_       s2   a b -> And_      <$>          o s2           <*> c a <*> c b
  Bottom_    s2       -> Bottom_   <$>          o s2
  Ceil_   s1 s2   a   -> Ceil_     <$> i s1 <*> o s2           <*> c a
  -- DV_        s2   a   -> DV_       <$>          o s2           <*> c a
  Fix (DomainValuePattern (DomainValue s2 a )) -> DV_ <$> o s2 <*> c a
  Equals_ s1 s2   a b -> Equals_   <$> i s1 <*> o s2           <*> c a <*> c b
  Exists_    s2 v a   -> Exists_   <$>          o s2 <*> var v <*> c a
  Floor_  s1 s2   a   -> Floor_    <$> i s1 <*> o s2           <*> c a
  Forall_    s2 v a   -> Forall_   <$>          o s2 <*> var v <*> c a
  Iff_       s2   a b -> Iff_      <$>          o s2           <*> c a <*> c b
  Implies_   s2   a b -> Implies_  <$>          o s2           <*> c a <*> c b
  In_     s1 s2   a b -> In_       <$> i s1 <*> o s2           <*> c a <*> c b
  -- Next_      s2   a   -> Next_     <$>          o s2           <*> c a
  Fix (NextPattern (Next s2 a)) -> Next_ <$> o s2 <*> c a
  Not_       s2   a   -> Not_      <$>          o s2           <*> c a
  Or_        s2   a b -> Or_       <$>          o s2           <*> c a <*> c b
  -- Rewrites_  s2   a b -> Rewrites_ <$>          o s2           <*> c a <*> c b
  Fix (RewritesPattern (Rewrites s2 a b)) -> Rewrites_ <$> o s2 <*> c a <*> c b
  Top_       s2       -> Top_      <$>          o s2
  Var_          v     -> Var_      <$>                   var v
  App_ h children -> App_ h <$> traverse c children
  -- StringLiteral_ s -> pure (StringLiteral_ s)
  -- CharLiteral_   c -> pure (CharLiteral_   c)
  p -> pure p

-- | The sort of a,b in \equals(a,b), \ceil(a) etc.
inputSort        f = patternLens f    pure pure pure
-- | The sort returned by a top level constructor.
-- NOTE ABOUT NOTATION:
-- In the this haskell code, this is always `s2`.
-- In the semantics.pdf documentation, the sorts are written
-- {s1} if there is one sort parameter, and {s1, s2}
-- if there are two sort parameters. This has the effect
-- that the result sort is sometimes s1 and sometimes s2.
-- I believe this convention is less confusing.
-- Note that a few constructors like App, StringLiteral and Var
-- Lack a result sort.
resultSort       f = patternLens pure f    pure pure
-- | Points to the bound variable in Forall/Exists,
-- and also the Variable in VariablePattern
variable         f = patternLens pure pure f    pure
-- All sub-expressions which are Patterns.
-- use partsOf allChildren to get a lens to a List.
allChildren      f = patternLens pure pure pure f


-- | Applies a function at an `[Int]` path.
localInPattern
    :: MetaOrObject level
    => [Int]
    -> (PureMLPattern level var -> PureMLPattern level var)
    -> PureMLPattern level var
    -> PureMLPattern level var
localInPattern path f pat = pat & inPath path %~ f


-- | Takes an `[Int]` representing a path, and returns a lens to that position.
-- The ints represent subpatterns in the obvious way:
-- [0,1] points to b in \ceil(a /\ b), etc.
inPath
    :: (MetaOrObject level, Applicative f)
    => [Int]
    -> (PureMLPattern level var -> f (PureMLPattern level var))
    -> (PureMLPattern level var -> f (PureMLPattern level var))
inPath []       = id --aka the identity lens
inPath (n : ns) = partsOf allChildren . ix n . inPath ns

-- | Rigid patterns are those which have a
-- single uniquely determined sort,
-- which we can't change.
isRigid
    :: MetaOrObject level
    => PureMLPattern level var
    -> Bool
isRigid p = case unFix p of
    ApplicationPattern   _ -> True
    DomainValuePattern   _ -> True
    VariablePattern      _ -> True
    StringLiteralPattern _ -> True
    CharLiteralPattern   _ -> True
    _                      -> False


-- | Flexible patterns are those which can be
-- any sort, like predicates \equals, \ceil etc.
-- The 3rd possibility (not isFlexible && not isRigid)
-- is a constructor whose sort
-- must match the sort of of its subexpressions:
-- \and, \or, \implies, etc.
isFlexible
    :: MetaOrObject level
    => PureMLPattern level var
    -> Bool
isFlexible p = case unFix p of
    BottomPattern _ -> True
    CeilPattern   _ -> True
    EqualsPattern _ -> True
    FloorPattern  _ -> True
    InPattern     _ -> True
    TopPattern    _ -> True
    _               -> False

-- | Tries to modify p to have sort s.
forceSort
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => Sort level
    -> PureMLPattern level var
    -> Maybe (PureMLPattern level var)
forceSort s p
   | isRigid    p = checkIfAlreadyCorrectSort s p
   | isFlexible p = Just $ p & resultSort .~ s
   | otherwise = traverseOf allChildren (forceSort s) p

checkIfAlreadyCorrectSort
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => Sort level
    -> PureMLPattern level var
    -> Maybe (PureMLPattern level var)
checkIfAlreadyCorrectSort s p
   | getSort p == s = Just p
   | otherwise = Nothing

-- | Modify all patterns in a list to have the same sort.
makeSortsAgree
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => [PureMLPattern level var]
    -> Maybe [PureMLPattern level var]
makeSortsAgree ps =
    forM ps $ forceSort $
        case asum $ getRigidSort <$> ps of
          Nothing -> flexibleSort
          Just a  -> a

getRigidSort
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => PureMLPattern level var
    -> Maybe (Sort level)
getRigidSort p =
    case forceSort flexibleSort p of
      Nothing -> Just $ getSort p
      Just _  -> Nothing

-- | Ensures that the subpatterns of a pattern match in their sorts
-- and assigns the correct sort to the top level pattern
-- i.e. converts the invalid (x : Int /\ ( x < 3 : Float)) : Bool
-- to the valid (x : Int /\ (x < 3 : Int)) : Int
ensureSortAgreement
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
ensureSortAgreement p =
  case makeSortsAgree $ p ^. partsOf allChildren of
    Just []    -> p & resultSort .~ flexibleSort
    Just children ->
      p & (partsOf allChildren) .~ children
        & inputSort  .~ childSort
        & resultSort .~ (
          if isFlexible p
            then flexibleSort
            else childSort
          )
      where childSort = getSort $ head children
    Nothing -> error $ "Can't unify sorts of subpatterns: " ++ show p

-- | Constructors that handle sort information automatically.
-- To use, put `give metadatatools` at the top of the computation.
mkAnd
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkAnd a b = ensureSortAgreement $ And_ fixmeSort a b

mkApp
    :: (MetaOrObject level, Given (MetadataTools level))
    => SymbolOrAlias level
    -> [PureMLPattern level var]
    -> PureMLPattern level var
mkApp = App_

mkBottom
    :: MetaOrObject level
    => PureMLPattern level var
mkBottom = Bottom_ flexibleSort

mkCeil
    :: (MetaOrObject level, Given (MetadataTools level), SortedVariable var)
    => PureMLPattern level var
    -> PureMLPattern level var
mkCeil a = Ceil_ (getSort a) flexibleSort a

mkDomainValue
    :: (MetaOrObject Object, Given (MetadataTools Object), SortedVariable var)
    => PureMLPattern Object var
    -> PureMLPattern Object var
mkDomainValue a = DV_ (getSort a) a

mkEquals
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkEquals a b = ensureSortAgreement $ Equals_ fixmeSort fixmeSort a b

mkExists
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => var level
    -> PureMLPattern level var
    -> PureMLPattern level var
mkExists v a = ensureSortAgreement $ Exists_ fixmeSort v a

mkFloor
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
mkFloor a = ensureSortAgreement $ Floor_ fixmeSort fixmeSort a

mkForall
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => var level
    -> PureMLPattern level var
    -> PureMLPattern level var
mkForall v a = ensureSortAgreement $ Forall_ fixmeSort v a

mkIff
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkIff a b = ensureSortAgreement $ Iff_ fixmeSort a b

mkImplies
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkImplies a b = ensureSortAgreement $ Implies_ fixmeSort a b

mkIn
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkIn a b = ensureSortAgreement $ In_ fixmeSort fixmeSort a b

mkNext
    ::  ( MetaOrObject Object
        , Given (MetadataTools Object)
        , SortedVariable var
        , Show (var Object))
    => PureMLPattern Object var
    -> PureMLPattern Object var
mkNext a = ensureSortAgreement $ Next_ fixmeSort a

mkNot
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
mkNot a = ensureSortAgreement $ Not_ fixmeSort a

mkOr
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        , SortedVariable var
        , Show (var level))
    => PureMLPattern level var
    -> PureMLPattern level var
    -> PureMLPattern level var
mkOr a b = ensureSortAgreement $ Or_ fixmeSort a b

mkRewrites
    ::  ( MetaOrObject Object
        , Given (MetadataTools Object)
        , SortedVariable var
        , Show (var Object))
    => PureMLPattern Object var
    -> PureMLPattern Object var
    -> PureMLPattern Object var
mkRewrites a b = ensureSortAgreement $ Rewrites_ fixmeSort a b

mkTop
    :: MetaOrObject level
    => PureMLPattern level var
mkTop = Top_ flexibleSort

mkVar
    :: (MetaOrObject level, Given (MetadataTools level))
    => var level
    -> PureMLPattern level var
mkVar = Var_

mkStringLiteral = StringLiteral_
mkCharLiteral   = CharLiteral_

mkSort
  :: MetaOrObject level
  => String
  -> Sort level
mkSort name =
    SortVariableSort $ SortVariable
        { getSortVariable = noLocationId name }

-- | Placeholder. Should never appear in output of 'mk' funcs
fixmeSort
    :: MetaOrObject level
    => Sort level
fixmeSort = mkSort "FIXME"
