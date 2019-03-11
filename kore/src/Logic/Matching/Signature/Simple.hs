{-|
Description: A generic signature for finite sets of simply-sorted labels

A generic signature for finite sets of simply-sorted labels.
This uses the reflection package to allow any set of string
sort names, string label names, and label signatures to
be used as an 'IsSignature' instance, on a type of the
form 'SimpleSignature s'.
Functions are also provided to check and convert strings
to the 'Label' or 'Sort' types associated with that signature.
-}
module Logic.Matching.Signature.Simple
    ( SignatureInfo(..)
    , ValidatedSignature, fromValidated, validate
    , SimpleSignature
    , ReifiesSignature
    , resolveLabel,resolveSort
    , reifySignature
    ) where

import           Data.Char
import           Data.Coerce
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Data.Text.Prettyprint.Doc

import Logic.Matching.Signature

-- | A finite signatures of sorts and labels written as text
data SignatureInfo = SignatureInfo
    { sorts  :: Set Text -- ^ The sort names
    , labels :: Map Text (Text,[Text])
      {- ^ The label names, mapped to a pair of the return sort and
           a list of argument sorts -}
    }
  deriving Show

-- | A newtype wrapper around signatures which are
-- valid in the sense the label sorts only mention
-- defined sorts.
newtype ValidatedSignature = ValidatedSignature SignatureInfo
instance Show ValidatedSignature where
  show (ValidatedSignature sig) = show sig

fromValidated :: ValidatedSignature -> SignatureInfo
fromValidated (ValidatedSignature info) = info

data SimpleSignature s

isValid :: SignatureInfo -> Bool
isValid sigInfo =
  all (\(result,args) -> sortOk result && all sortOk args) (labels sigInfo)
 where sortOk sort = Set.member sort (sorts sigInfo)

validate :: SignatureInfo -> Maybe ValidatedSignature
validate sig = if isValid sig then Just (ValidatedSignature sig) else Nothing

type ReifiesSignature s = Reifies s ValidatedSignature

reifySignature :: ValidatedSignature
               -> (forall (s :: *). (Reifies s ValidatedSignature)
                           => Proxy (SimpleSignature s) -> a)
               -> a
reifySignature sig f = reify sig (\(_proxy :: Proxy s) -> f @s Proxy)

instance (Reifies s ValidatedSignature) => IsSignature (SimpleSignature s) where
  newtype Label (SimpleSignature s) = SimpleLabel Text
  newtype Sort (SimpleSignature s) = SimpleSort Text
  labelSignature (SimpleLabel name) =
    case Map.lookup name (labels sig) of
      Just signature -> coerce signature
      Nothing -> error $ "This should be impossible!"
        ++" Encapsulation failure, invalid label "++show name
        ++" found in a reflected signature"
   where sig = fromValidated (reflect @s Proxy)
deriving instance (Eq (Label (SimpleSignature s)))
deriving instance (Eq (Sort (SimpleSignature s)))

instance Show (Label (SimpleSignature s)) where
  show (SimpleLabel l) = show l
instance Show (Sort (SimpleSignature s)) where
  show (SimpleSort l) = show l

-- | Print alphanumeric names without quoting and
-- other names as quoted strings.
instance Pretty (Label (SimpleSignature s)) where
  pretty (SimpleLabel l)
    | isAlpha (Text.head l) && Text.all isAlphaNum l = pretty l
    | otherwise = pretty (show l)
-- | Print alphanumeric names without quoting and
-- other names as quoted strings
instance Pretty (Sort (SimpleSignature s)) where
  pretty (SimpleSort l)
    | isAlpha (Text.head l) && Text.all isAlphaNum l = pretty l
    | otherwise = pretty (show l)

instance (Reifies s ValidatedSignature) => CheckableSignature (SimpleSignature s) where
    type RawLabel (SimpleSignature s) = Text
    type RawSort (SimpleSignature s) = Text
    resolveSort sortName =
        {- this uses lookupGE to return the existing value from in the set,
           to avoid keeping multiple Text values with identical contents -}
        case Set.lookupGE sortName (sorts sig) of
            Just sort' | sort' == sortName -> Just (SimpleSort sort')
            _          -> Nothing
      where sig = fromValidated (reflect @s Proxy)

    resolveLabel labelName =
        {- this uses lookupGE to return the existing value from in the set,
           to avoid keeping multiple Text values with identical contents -}
        case Map.lookupGE labelName (labels sig) of
            Just (label',_) | label' == labelName -> Just (SimpleLabel label')
            _               -> Nothing
      where sig = fromValidated (reflect @s Proxy)
