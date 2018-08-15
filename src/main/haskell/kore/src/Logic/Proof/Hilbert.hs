{-|
Description: A generic representation of Hilbert proofs

A generic representation Hilbert proofs. The proof type is parameterized over a
choice of formulas, proof rules, and line labels, and provides a proof-building
interface that maintains a well-formed proof structure. Checking uniqueness of
labels and that proposed derivations refer to only allowed (i.e, earlier) labels
is handled by code in this module. A type class is defined and relied upon for
checking whether a given proof rule instance actually supports a conclusion.
-}
module Logic.Proof.Hilbert
    ( Proof(index, claims, derivations)
    , ProofSystem(..)
    , emptyProof
    , add
    , derive
    , renderProof
    ) where

import           Data.Foldable
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Sequence
                 ( Seq, (|>) )
import qualified Data.Sequence as Seq
import           Data.Text.Prettyprint.Doc

import Kore.Error
import Logic.Matching.Error

data Proof ix rule formula =
  Proof
  { index       :: Map ix (Int,formula)
  , claims      :: Seq (ix,formula)
  , derivations :: Map ix (rule ix)
  }
  deriving (Show)

emptyProof :: Proof ix rule formula
emptyProof = Proof Map.empty Seq.empty Map.empty

add :: (Pretty ix, Ord ix)
    => (formula -> Either (Error error) ())
    -> Proof ix rule formula -> ix -> formula
    -> Either (Error error) (Proof ix rule formula)
add verifier proof ix formula = do
  mlFailWhen
    (Map.member ix (index proof))
    ["A formula with ID ", squotes (pretty ix), " already exists"]
  verifier formula
  return proof
    { index = Map.insert ix (Seq.length (claims proof), formula) (index proof)
    , claims = claims proof |> (ix,formula)
    , derivations = derivations proof
    }

renderProof :: (Ord ix, Pretty ix, Pretty (rule ix), Pretty formula)
            => Proof ix rule formula -> Doc ann
renderProof proof = vcat
  [pretty ix<+>colon<+>pretty formula<>
   case Map.lookup ix (derivations proof) of
     Nothing   -> emptyDoc
     Just rule -> emptyDoc <+> "by" <+> pretty rule
  | (ix,formula) <- toList (claims proof)]

class (Traversable rule, Eq formula)
    => ProofSystem error rule formula | rule -> formula error
  where
    checkDerivation
        :: formula
        -> rule formula
        -> Either (Error error) ()

derive :: (Pretty ix, Ord ix, ProofSystem error rule formula)
       => Proof ix rule formula
       -> ix -> rule ix
       -> Either (Error error) (Proof ix rule formula)
derive proof ix rule = do
  mlFailWhen (Map.member ix (derivations proof))
    [ "Formula with ID "
    , squotes (pretty ix)
    , " already has a derivation."
    ]
  (offset,conclusion) <-
    case Map.lookup ix (index proof) of
      Nothing ->
        mlFail ["Formula with ID ", squotes (pretty ix), " not found."]
      Just a  -> return a
  let resolveIx name = do
        (offset',formula') <-
          case Map.lookup name (index proof) of
            Nothing ->
              mlFail
                ["Formula with ID ", squotes (pretty name), " not found."]
            Just a -> return a
        mlFailWhen (offset' >= offset)
          [ "One of the hypotheses "
          , parens (pretty name)
          , " was not defined before the conclusion "
          , parens (pretty ix)
          , "."
          ]
        return formula'
  resolvedRule <- traverse resolveIx rule
  checkDerivation conclusion resolvedRule
  return (proof { derivations = Map.insert ix rule (derivations proof) })
