{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Syntax.Definition
    ( Definition (..)
    -- * Type synonyms
    , PureDefinition
    -- * Re-exports
    , module Kore.Syntax.Sentence
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
                 ( Hashable (..) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Attribute.Attributes
import Kore.Syntax.Module
import Kore.Syntax.Sentence
import Kore.Unparser


{- | Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition (sentence :: *) =
    Definition
        { definitionAttributes :: !Attributes
        , definitionModules    :: ![Module sentence]
        }
    deriving (Eq, Functor, Foldable, Generic, Show, Traversable)

instance Hashable sentence => Hashable (Definition sentence)

instance NFData sentence => NFData (Definition sentence)

instance Unparse sentence => Unparse (Definition sentence) where
    unparse Definition { definitionAttributes, definitionModules } =
        Pretty.vsep
            (unparse definitionAttributes : map unparse definitionModules)

    unparse2 Definition { definitionAttributes, definitionModules } =
        Pretty.vsep
            (unparse2 definitionAttributes : map unparse2 definitionModules)

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition level domain = Definition (PureSentence domain)
