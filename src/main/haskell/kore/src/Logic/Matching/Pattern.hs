{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}
{-|
Description: Abstract syntax of matching logic patterns

An implementation of matching logic patterns as described in \"The Semantics of
K\", without the provisions in language-kore for handling the surface syntax of
Kore (such as mixed object-level and meta-level terms).
-}
module Logic.Matching.Pattern
    ( PatternF(..)
    , Pattern
    , visitPatternF
    , patternSort
    , IsSignature(..)
    , SigPatternF
    , SigPattern
    , WFPattern
    , fromWFPattern -- note the constructor is *not* exported
    , wfPatSort
    , checkSorts1
    , checkSorts
    , resolvePattern
    , ToPattern(..)
    , FromPattern(..)
    , notFree
    , pattern VariableP
    , pattern ApplicationP
    , pattern AndP
    , pattern NotP
    , pattern ExistsP
    , variableP
    , applicationP
    , andP
    , notP
    , existsP
    , pattern OrP
    , pattern ImpliesP
    , pattern IffP
    , pattern ForallP
    , orP
    , impliesP
    , iffP
    , forallP
    , andP' , notP', orP', impliesP', iffP', forallP', existsP'
    ) where

import Control.Monad
import Data.Coerce
import Data.Deriving
       ( deriveEq1, deriveShow1 )
import Data.Functor.Foldable
import Data.Text.Prettyprint.Doc

import Data.Functor.Foldable.Orphans ()
import Logic.Matching.Signature

-- | The base functor of patterns
--
-- Argument description:
--
--  - @sort@ represents the type of sorts
--
--  - @label@ represents the type of labels
--    (sometimes used for aliases as well as symbols)
--
--  - @v@ represents the type of variables
--
--  - @p@ represents the type of subterms
data PatternF sort label v p
  = Variable sort v
  | Application label [p]
  | And sort p p
  | Not sort p
  | Exists sort sort v p
  deriving (Eq, Show, Functor, Foldable, Traversable)

deriveEq1 ''PatternF
deriveShow1 ''PatternF

visitPatternF :: (Applicative f)
              => (sort -> f sort')
              -> (label -> f label')
              -> (var -> f var')
              -> (pat -> f pat')
              -> (PatternF sort label var pat
                   -> f (PatternF sort' label' var' pat'))
visitPatternF sort label var pat term = case term of
  Variable s v       -> Variable <$> sort s <*> var v
  Application l args -> Application <$> label l <*> traverse pat args
  And s p1 p2        -> And <$> sort s <*> pat p1 <*> pat p2
  Not s p            -> Not <$> sort s <*> pat p
  Exists s sVar v p  -> Exists <$> sort s <*> sort sVar <*> var v <*> pat p

-- | Specializing 'PatternF' to use the sort and label from a signature 'sig'.
type SigPatternF sig = PatternF (Sort sig) (Label sig)

-- | A simple fixpoint of 'PatternF'
type Pattern sort label v = Fix (PatternF sort label v)
-- | A simple fixpoint of 'SigPatternF'
type SigPattern sig v = Fix (SigPatternF sig v)

-- | Get the result sort of a non-necessarily-well-formed pattern.
-- The 'IsSignature' constraint is requried to look up label
-- information, because 'Application' does not store a result sort.
patternSort :: (IsSignature sig) => SigPatternF sig v p -> Sort sig
patternSort p = case p of
    Variable s _    ->    s
    Application l _ -> labelResult l
    And s _ _       -> s
    Not s _         -> s
    Exists s _ _ _  -> s

-- | Patterns which are well-formed with respect to signature 'sig'
newtype WFPattern sig var = WFPattern {fromWFPattern :: SigPattern sig var}
deriving instance (Eq (Sort sig), Eq (Label sig), Eq var) => Eq (WFPattern sig var)
deriving instance (Show (Sort sig), Show (Label sig), Show var) => Show (WFPattern sig var)
deriving instance (Pretty (SigPatternF sig var (SigPattern sig var)))
                  -- expanded according to Pretty (f (Fix f)) => Pretty (Fix f)
                  -- to avoid warning
                => Pretty (WFPattern sig var)

-- | Get sort of a well-formed pattern
wfPatSort :: (IsSignature sig) => WFPattern sig var -> Sort sig
wfPatSort (WFPattern (Fix p)) = patternSort p

-- | Check the sorts of one layer of a pattern,
-- requiring that the subterms are already known to be well-formed
checkSorts1 :: (IsSignature sig, Eq (Sort sig))
            => SigPatternF sig var (WFPattern sig var)
            -> Maybe (WFPattern sig var)
checkSorts1 pat = if patOk then Just (WFPattern (Fix (coerce pat))) else Nothing
  where
    patOk = case pat of
      Variable _ _ -> True
      Application l ps ->
        and (zipWith (==) (labelArguments l) (map wfPatSort ps))
      And _ _ _ -> childrenSame
      Not _ _ -> childrenSame
      Exists _ _ _ _ -> childrenSame
    childrenSame = all (==patternSort pat) (fmap wfPatSort pat)

-- | Check if a pattern is well-sorted
checkSorts :: (IsSignature sig, Eq (Sort sig))
           => SigPattern sig var
           -> Maybe (WFPattern sig var)
checkSorts pat = cata (sequenceA >=> checkSorts1) pat

{- | Check if all the raw sorts and labels in a pattern are
     labels in the given signature -}
resolvePattern :: forall sig var . CheckableSignature sig
                 => Pattern (RawSort sig) (RawLabel sig) var
                 -> Maybe (SigPattern sig var)
resolvePattern = cata (sequenceA >=> recognizeLayer >=> return . Fix)
  where
    recognizeLayer = visitPatternF resolveSort resolveLabel pure pure

class ToPattern p sort label var | p -> sort label var where
  toPattern :: p -> PatternF sort label var p
class FromPattern p sort label var | p -> sort label var where
  fromPattern :: PatternF sort label var p -> p

notFree :: (Eq sort, Eq var, ToPattern p sort label var)
        => sort -> var -> p -> Bool
notFree sVar var p = go (toPattern p)
  where go (Variable sVar' var') = not (sVar' == sVar && var' == var)
        go (Exists _ sVar' var' _)
          | sVar' == sVar, var' == var = True
        go pat = all (go . toPattern) pat

instance ToPattern (Pattern sort label var) sort label var where
    toPattern (Fix pat) = pat
instance FromPattern (Pattern sort label var) sort label var where
    fromPattern = Fix

instance ToPattern (WFPattern sig var) (Sort sig) (Label sig) var where
    toPattern (WFPattern p) = coerce p
instance (IsSignature sig, Eq (Sort sig)) =>
    FromPattern (Maybe (WFPattern sig var)) (Sort sig) (Label sig) var
  where
    fromPattern = sequenceA >=> checkSorts1
instance (Applicative f) => FromPattern (f (Pattern sort label var)) sort label var where
    fromPattern p = Fix <$> sequenceA p

pattern VariableP :: (ToPattern p sort label var) => sort -> var -> p
pattern VariableP sort var <- (toPattern -> Variable sort var)

pattern ApplicationP :: (ToPattern p sort label var) => label -> [p] -> p
pattern ApplicationP label args <- (toPattern -> Application label args)

pattern AndP :: (ToPattern p sort label var) => sort -> p -> p -> p
pattern AndP s p1 p2 <- (toPattern -> And s p1 p2)

pattern NotP :: (ToPattern p sort label var) => sort -> p -> p
pattern NotP s p <- (toPattern -> Not s p)

pattern ExistsP :: (ToPattern p sort label var) => sort -> sort -> var -> p -> p
pattern ExistsP s sVar var p <- (toPattern -> Exists s sVar var p)

variableP :: (FromPattern p sort label var) => sort -> var -> p
variableP sort var = fromPattern (Variable sort var)
applicationP :: (FromPattern p sort label var) => label -> [p] -> p
applicationP label args = fromPattern (Application label args)
andP :: (FromPattern p sort label var) => sort -> p -> p -> p
andP s p1 p2 = fromPattern (And s p1 p2)
notP :: (FromPattern p sort label var) => sort -> p -> p
notP s p = fromPattern (Not s p)
existsP :: (FromPattern p sort label var) => sort -> sort -> var -> p -> p
existsP s sVar var p = fromPattern (Exists s sVar var p)

pattern OrP :: (ToPattern p sort label var, Eq sort) => sort -> p -> p -> p
pattern OrP s p1 p2 <- NotP s (AndP ((==s)->True)
                                (NotP ((==s)->True) p1)
                                (NotP ((==s)->True) p2))

orP :: FromPattern p sort label var => sort -> p -> p -> p
orP s p1 p2 = notP s (andP s (notP s p1) (notP s p2))

pattern ImpliesP :: (ToPattern p sort label var, Eq sort) => sort -> p -> p -> p
pattern ImpliesP s p1 p2 <- OrP s (NotP ((==s)->True) p1) p2
impliesP :: FromPattern p sort label var => sort -> p -> p -> p
impliesP s p1 p2 = orP s (notP s p1) p2

pattern IffP :: (ToPattern p sort label var, Eq p, Eq sort) => sort -> p -> p -> p
pattern IffP s p1 p2 <- AndP s (ImpliesP ((==s)->True) p1 p2)
                               (ImpliesP ((==s)->True) ((==p2)->True) ((==p1)->True))
iffP :: FromPattern p sort label var => sort -> p -> p -> p
iffP s p1 p2 = andP s (impliesP s p1 p2) (impliesP s p2 p1)

pattern ForallP :: (ToPattern p sort label var, Eq sort) => sort -> sort -> var -> p -> p
pattern ForallP s sVar var p <-
    NotP s (ExistsP ((==s)->True) sVar var (NotP ((==s)->True) p))

forallP :: (FromPattern p sort label var) => sort -> sort -> var -> p -> p
forallP s sVar var p = notP s (existsP s sVar var (notP s p))

type IsSigPatternIn m p sig var =
  ( IsSignature sig
  , FromPattern (m p) (Sort sig) (Label sig) var
  , ToPattern p (Sort sig) (Label sig) var
  , Monad m
  )

{- | Helpers for making more automatic builders that take the return sort
  from the first subpattern.
  This specializes types to require a 'FromPattern' instance using the
  sorts and labels from an 'IsSignature' instance rather than working
  more generally, so both versions are useful.
 -}
-- | Lift a builder with two subpatterns
autoSort2 :: (IsSigPatternIn m p sig var)
          => (Sort sig -> m p -> m p -> m p)
          -> (m p -> m p -> m p)
autoSort2 builder pat1 pat2 = do
    sort <- patternSort . toPattern <$> pat1
    builder sort pat1 pat2
-- | Lift a builder with one subpattern
autoSort1 :: (IsSigPatternIn m p sig var)
          => (Sort sig -> m p -> m p)
          -> (m p -> m p)
autoSort1 builder pat = do
    sort <- patternSort . toPattern <$> pat
    builder sort pat

andP', orP', impliesP', iffP'
    :: (IsSigPatternIn m p sig var) => m p -> m p -> m p
andP' = autoSort2 andP
orP' = autoSort2 orP
impliesP' = autoSort2 impliesP
iffP' = autoSort2 iffP

notP' :: (IsSigPatternIn m p sig var)
      => m p -> m p
notP' = autoSort1 notP

forallP' :: (IsSigPatternIn m p sig var)
         => Sort sig -> var -> m p -> m p
forallP' sVar var = autoSort1 (\s -> forallP s sVar var)

existsP' :: (IsSigPatternIn m p sig var)
         => Sort sig -> var -> m p -> m p
existsP' sVar var = autoSort1 (\s -> existsP s sVar var)
