{-|
Description: Signatures of matching logic theories
-}
module Logic.Matching.Signature where

{-| A matching logic signature is a set of sorts and a set of labels where each
  label is associated with a result sort and a list of argument sorts.
-}
class (Eq (Sort sig), Eq (Label sig)) => IsSignature sig where
  -- | The type of labels in the matching logic signature @sig@.
  data Label sig :: *
  -- | The type of sorts in the matching logic signature @sig@.
  data Sort sig :: *

  {-| The result and argument sorts of a label.

    prop> labelSignature l = (labelResult l, labelArguments l)
  -}
  labelSignature :: Label sig -> (Sort sig,[Sort sig])

  labelResult :: Label sig -> Sort sig
  labelResult l = fst (labelSignature l)

  labelArguments :: Label sig -> [Sort sig]
  labelArguments l = snd (labelSignature l)

class (IsSignature sig) => CheckableSignature sig where
  type RawLabel sig :: *
  type RawSort sig :: *
  resolveLabel :: RawLabel sig -> Maybe (Label sig)
  resolveSort :: RawSort sig -> Maybe (Sort sig)
