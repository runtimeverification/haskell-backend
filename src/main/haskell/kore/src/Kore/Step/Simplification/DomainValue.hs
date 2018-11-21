{-|
Module      : Kore.Step.Simplification.DomainValue
Description : Tools for DomainValue pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.DomainValue
    ( simplify
    ) where

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( DomainValue (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: ( Ord (variable Object), Show (variable Object)
       , SortedVariable variable
       )
    => MetadataTools Object attrs
    -> DomainValue Object Domain.Builtin (OrOfExpandedPattern Object variable)
    -> ( OrOfExpandedPattern Object variable
       , SimplificationProof Object
       )
simplify
    MetadataTools { symbolOrAliasSorts }
    DomainValue { domainValueSort, domainValueChild }
  =
    ( OrOfExpandedPattern.filterOr
        (do
            child <- give symbolOrAliasSorts simplifyBuiltin domainValueChild
            return (DV_ domainValueSort <$> child)
        )
    , SimplificationProof
    )

simplifyBuiltin
    :: ( Eq (variable Object), Show (variable Object)
       , Given (SymbolOrAliasSorts Object)
       , SortedVariable variable
       )
    => Domain.Builtin (OrOfExpandedPattern Object variable)
    -> MultiOr
        (Predicated Object variable
            (Domain.Builtin (StepPattern Object variable)))
simplifyBuiltin =
    \case
        Domain.BuiltinPattern pat -> (return . pure) (Domain.BuiltinPattern pat)
        Domain.BuiltinMap _map -> do
            _map <- sequence _map
            -- MultiOr propagates \bottom children upward.
            return (Domain.BuiltinMap <$> sequenceA _map)
        Domain.BuiltinList _list -> do
            _list <- sequence _list
            -- MultiOr propagates \bottom children upward.
            return (Domain.BuiltinList <$> sequenceA _list)
        Domain.BuiltinSet set -> (return . pure) (Domain.BuiltinSet set)
