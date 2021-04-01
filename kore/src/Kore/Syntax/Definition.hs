{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Syntax.Definition (
    Definition (..),

    -- * Type synonyms
    PureDefinition,
    ParsedDefinition,

    -- * Re-exports
    module Kore.Syntax.Sentence,
) where

import Data.Kind (
    Type,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Attributes
import Kore.Debug
import Kore.Syntax.Module
import Kore.Syntax.Sentence
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- | Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition (sentence :: Type) = Definition
    { definitionAttributes :: !Attributes
    , definitionModules :: ![Module sentence]
    }
    deriving (Eq, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse sentence => Unparse (Definition sentence) where
    unparse Definition{definitionAttributes, definitionModules} =
        Pretty.vsep
            (unparse definitionAttributes : map unparse definitionModules)

    unparse2 Definition{definitionAttributes, definitionModules} =
        Pretty.vsep
            (unparse2 definitionAttributes : map unparse2 definitionModules)

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition = Definition PureSentence

type ParsedDefinition = Definition ParsedSentence
