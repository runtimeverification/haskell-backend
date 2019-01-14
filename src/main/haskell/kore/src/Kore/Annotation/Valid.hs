{- |
Module      : Kore.Annotation.Valid
Description : Annotations collected during verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
 -}

module Kore.Annotation.Valid
    ( Valid (..)
    , mapVariables
    , traverseVariables
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

{- | @Valid@ is a pattern annotation of facts collected during verification.
 -}
data Valid variable level =
    Valid
        { patternSort :: !(Sort level)
        -- ^ The sort determined by the verifier.
        , freeVariables :: !(Set variable)
        -- ^ The free variables of the pattern.
        }
    deriving (Eq, Generic, Ord, Show)

instance NFData variable => NFData (Valid variable level)

instance Hashable variable => Hashable (Valid variable level) where
    hashWithSalt salt Valid { patternSort, freeVariables } =
        flip hashWithSalt patternSort
        $ flip hashWithSalt (Set.toList freeVariables)
        $ salt

{- | Use the provided mapping to replace all variables in a 'PurePattern'.

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> Valid variable1 level -> Valid variable2 level
mapVariables mapping valid =
    valid { freeVariables = Set.map mapping freeVariables }
  where
    Valid { freeVariables } = valid

{- | Use the provided traversal to replace the free variables in a 'Valid'.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m level variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> Valid variable1 level
    -> m (Valid variable2 level)
traverseVariables traversing valid@Valid { freeVariables } =
    (\freeVariables' -> valid { freeVariables = Set.fromList freeVariables' })
        <$> traverse traversing (Set.toList freeVariables)
