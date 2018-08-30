{-|
Description: A generic signature for parameterized sorts and labels

A generic signature for parameterized sorts and labels.
This uses the reflection package to provide a type with
an 'IsSignature' instance from a set of textual label
and sort names, along with the number of parameters of
each sort and the number of sort parameters
and a parameterized signature for each label.
Functions are also provided to check and convert trees
over strings into the 'Label' or 'Sort' types associated
with that signature.
-}
module Logic.Matching.Signature.Polymorphic
    ( SortPat
    , SignatureInfo(..)
    , ValidatedSignature, fromValidated, validate
    , PolySignature
    , ReifiesSignature
    , resolveLabel,resolveSort
    , reifySignature
    , prettyPolyTerm
    ) where

import           Data.Char
                 ( isAlpha, isAlphaNum )
import           Data.Coerce
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Data.Text.Prettyprint.Doc

import Logic.Matching.Pattern
import Logic.Matching.Signature

-- | A tree of applied sort constructors,
-- which also allows for sort variables.
data SortPat = PApp Text [SortPat] | Var Int
  deriving Show

-- | A signature of parameterized sorts and labels.
data SignatureInfo = SignatureInfo
  { sortCons :: Map Text Int -- ^ Map from sort to arity
  , labels   :: Map Text (Int,SortPat,[SortPat])
    {- ^ Map from a label to a tuple of arity,
       result sort, and argument sorts,
       which are given 'SortPat' which may
       use varible indices from 0 to less than the arity.
    -}
  }
  deriving Show

newtype ValidatedSignature =
    ValidatedSignature {fromValidated :: SignatureInfo}
instance Show ValidatedSignature where
  show (ValidatedSignature sig) = show sig

data PolySignature s

sortTermValid :: Map Text Int -> Int -> SortPat -> Bool
sortTermValid sortArities nargs t = check t
  where check (Var v) = 0 <= v && v < nargs
        check (PApp c ts) =
          case Map.lookup c sortArities of
            Just arity -> arity == length ts && all check ts
            Nothing    -> False

isValid :: SignatureInfo -> Bool
isValid sigInfo =
    all (\(arity,result,args) -> all (sortOk arity) (result:args)) (labels sigInfo)
  where sortOk arity t = sortTermValid (sortCons sigInfo) arity t

validate :: SignatureInfo -> Maybe ValidatedSignature
validate sig = if isValid sig then Just (ValidatedSignature sig) else Nothing

data RawPolySort = RawPolySort Text [RawPolySort]
  deriving Eq
data RawPolyLabel = RawPolyLabel Text [RawPolySort]
  deriving Eq

prettyName :: Text -> Doc ann
prettyName name
  | isAlpha (Text.head name) && Text.all isAlphaNum name = pretty name
  | otherwise = pretty (show name)

prettyPolyTerm :: (Pretty t) => Text -> [t] -> Doc ann
prettyPolyTerm name args = prettyName name <> braced (map pretty args)

instance Show RawPolySort where
  showsPrec _ (RawPolySort con args) s = shows con (showsBraces args s)
instance Pretty RawPolySort where
  pretty (RawPolySort con args) = prettyName con <> (braced (map pretty args))

showsBraces :: (Show a) => [a] -> ShowS
showsBraces items rest = '{':showsItems items ('}':rest)
   where showsItems [] s          = s
         showsItems [x] s         = shows x s
         showsItems (x:l@(_:_)) s = shows x (',':showsItems l s)

instantiate :: [RawPolySort] -> SortPat -> RawPolySort
instantiate args (Var v)          = args !! v
instantiate args (PApp con cargs) = RawPolySort con (map (instantiate args) cargs)

type ReifiesSignature s = Reifies s ValidatedSignature

deriving instance Eq (Label (PolySignature s))
instance Show (Label (PolySignature s)) where
  showsPrec _ (PolyLabel l args) s = shows l (showsBraces args s)
deriving instance Eq (Sort (PolySignature s))
instance Show (Sort (PolySignature s)) where
  show (PolySort s) = show s

braced :: [Doc ann] -> Doc ann
braced = group . encloseSep lbrace rbrace comma

instance Pretty (Label (PolySignature s)) where
  pretty (PolyLabel l args) = prettyName l <> braced (map pretty args)
instance Pretty (Sort (PolySignature s)) where
  pretty (PolySort s) = pretty s

instance (Reifies s ValidatedSignature) => IsSignature (PolySignature s) where
  data Label (PolySignature s) = PolyLabel Text [RawPolySort]
  newtype Sort (PolySignature s) = PolySort RawPolySort
  labelSignature (PolyLabel name sortArgs) =
    case Map.lookup name (labels sig) of
      Just (arity,result,args)
          | arity == length sortArgs -> coerce
            (instantiate sortArgs result, map (instantiate sortArgs) args)
          | otherwise -> error $ "Encapsulation failure, label "++show name++" applied to incorrect number "++show (length args)++" of sort parameters"
      Nothing -> error $ "Encapsulation failure, invalid label "++show name++" found in a reflected signature"
   where sig = fromValidated (reflect @s Proxy)

resolveSort1 :: forall s . (Reifies s ValidatedSignature) =>
  Text -> [Sort (PolySignature s)] -> Maybe (Sort (PolySignature s))
resolveSort1 sortName args =
  case Map.lookupGE sortName (sortCons sig) of
    Just (sort',arity) | sort' == sortName, arity == length args
                         -> Just (PolySort (RawPolySort sort' (coerce args)))
    _ -> Nothing
 where sig = fromValidated (reflect @s Proxy)

resolveLabel1 :: forall s . (Reifies s ValidatedSignature) =>
  Text -> [Sort (PolySignature s)] -> Maybe (Label (PolySignature s))
resolveLabel1 labelName args =
  case Map.lookupGE labelName (labels sig) of
    Just (label',(arity,_,_)) | label' == labelName, arity == length args
                                -> Just (PolyLabel label' (coerce args))
    _ -> Nothing
 where sig = fromValidated (reflect @s Proxy)

instance (Reifies s ValidatedSignature) => CheckableSignature (PolySignature s) where
    type RawLabel (PolySignature s) = RawPolyLabel
    type RawSort (PolySignature s) = RawPolySort
    resolveSort (RawPolySort name args) = traverse resolveSort args >>= resolveSort1 name
    resolveLabel (RawPolyLabel name args) = traverse resolveSort args >>= resolveLabel1 name

reifySignature :: forall a. ValidatedSignature
               -> (forall (s :: *). (Reifies s ValidatedSignature)
                           => Proxy (PolySignature s) -> a)
               -> a
reifySignature sig f = reify sig go
  where
    go :: forall (s :: *). Reifies s ValidatedSignature => Proxy s -> a
    go _ = f @s Proxy
