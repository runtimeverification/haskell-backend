{-|
Description: A generic representation of Hilbert proofs

A generic representation Hilbert proofs.
The proof type is parameterized over a choice of formulas,
proof rules, and line labels, and provides a proof-building
interface that maintains a well-formed proof structure.
Checking uniqueness of labels and that proposed derivations
refer to only allowed (i.e, earlier) labels is handled by
code in this module.
A type class is defined and relied upton for checking
whether a given proof rule instance actually supports
a conclusion.
-}
module Kore.MatchingLogic.HilbertProof
  (Proof(index,claims,derivations)
  ,ProofSystem(..)
  ,emptyProof
  ,add
  ,derive
  ,renderProof
  ) where
import           Control.Monad             (guard)
import           Data.Foldable
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import           Data.Sequence             (Seq, (|>))
import qualified Data.Sequence             as Seq

import           Data.Text.Prettyprint.Doc

data Proof ix rule formula =
  Proof
  { index       :: Map ix (Int,formula)
  , claims      :: Seq (ix,formula)
  , derivations :: Map ix (rule ix)
  }
  deriving (Show)

emptyProof :: Proof ix rule formula
emptyProof = Proof Map.empty Seq.empty Map.empty

add :: (Ord ix)
    => Proof ix rule formula -> ix -> formula -> Maybe (Proof ix rule formula)
add proof ix formula
  | not (Map.member ix (index proof)) = Just $
    proof { index = Map.insert ix (Seq.length (claims proof), formula) (index proof)
          , claims = claims proof |> (ix,formula)
          , derivations = derivations proof
          }
  | otherwise = Nothing

renderProof :: (Ord ix, Pretty ix, Pretty (rule ix), Pretty formula)
            => Proof ix rule formula -> Doc ann
renderProof proof = vcat
  [pretty ix<+>colon<+>pretty formula<>
   case Map.lookup ix (derivations proof) of
     Nothing   -> emptyDoc
     Just rule -> emptyDoc<+>pretty "by"<+>pretty rule
  | (ix,formula) <- toList (claims proof)]

class (Traversable rule, Eq formula) => ProofSystem rule formula | rule -> formula where
  checkDerivation :: formula -> rule formula -> Bool

derive :: (Ord ix, ProofSystem rule formula)
       => Proof ix rule formula
       -> ix -> formula -> rule ix
       -> Maybe (Proof ix rule formula)
derive proof ix f rule = do
  guard $ not (Map.member ix (derivations proof))
  (offset,conclusion) <- Map.lookup ix (index proof)
  guard (conclusion == f)
  let resolveIx name = do
        (offset',formula') <- Map.lookup name (index proof)
        guard (offset' < offset)
        return formula'
  resolvedRule <- traverse resolveIx rule
  guard $ checkDerivation conclusion resolvedRule
  return (proof { derivations = Map.insert ix rule (derivations proof) })
