{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Attribute.Pattern
    ( Pattern (..)
    , mapVariables
    , traverseVariables
    , deleteFreeVariable
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
                 ( Hashable (..) )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import Kore.Sort
       ( Sort )

{- | @Pattern@ are the attributes of a pattern collected during verification.
 -}
data Pattern variable =
    Pattern
        { patternSort :: !Sort
        -- ^ The sort determined by the verifier.
        , freeVariables :: !(Set variable)
        -- ^ The free variables of the pattern.
        }
    deriving (Eq, Generic, Ord, Show)

instance NFData variable => NFData (Pattern variable)

instance Hashable variable => Hashable (Pattern variable) where
    hashWithSalt salt Pattern { patternSort, freeVariables } =
        flip hashWithSalt patternSort
        $ flip hashWithSalt (Set.toList freeVariables)
        $ salt

{- | Use the provided mapping to replace all variables in a 'Pattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> Pattern variable1 -> Pattern variable2
mapVariables mapping valid =
    valid { freeVariables = Set.map mapping freeVariables }
  where
    Pattern { freeVariables } = valid

{- | Use the provided traversal to replace the free variables in a 'Pattern'.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> Pattern variable1
    -> m (Pattern variable2)
traverseVariables traversing valid@Pattern { freeVariables } =
    (\freeVariables' -> valid { freeVariables = Set.fromList freeVariables' })
        <$> traverse traversing (Set.toList freeVariables)

{- | Delete the given variable from the set of free variables.
 -}
deleteFreeVariable
    :: Ord variable
    => variable
    -> Pattern variable
    -> Pattern variable
deleteFreeVariable variable valid@Pattern { freeVariables } =
    valid { freeVariables = Set.delete variable freeVariables }
