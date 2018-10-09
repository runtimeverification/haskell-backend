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
                 ( BuiltinDomain (..), DomainValue (..), PureMLPattern,
                 SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: ( Eq (variable Object), Show (variable Object)
       , SortedVariable variable
       )
    => MetadataTools Object attrs
    -> DomainValue Object (BuiltinDomain (OrOfExpandedPattern Object variable))
    -> ( OrOfExpandedPattern Object variable
       , SimplificationProof Object
       )
simplify
    MetadataTools { symbolOrAliasSorts }
    DomainValue { domainValueSort, domainValueChild }
  =
    ( OrOfExpandedPattern.filterOr
        (do
            child <-
                give symbolOrAliasSorts simplifyBuiltinDomain domainValueChild
            return (DV_ domainValueSort <$> child)
        )
    , SimplificationProof
    )

simplifyBuiltinDomain
    :: ( Eq (variable Object), Show (variable Object)
       , Given (SymbolOrAliasSorts Object)
       , SortedVariable variable
       )
    => BuiltinDomain (OrOfExpandedPattern Object variable)
    -> MultiOr (Predicated Object variable (BuiltinDomain (PureMLPattern Object variable)))
simplifyBuiltinDomain =
    \case
        BuiltinDomainPattern pat -> (return . pure) (BuiltinDomainPattern pat)
        BuiltinDomainMap _map -> do
            _map <- sequence _map
            return (BuiltinDomainMap <$> sequenceA _map)
        BuiltinDomainList _list -> do
            _list <- sequence _list
            return (BuiltinDomainList <$> sequenceA _list)
        BuiltinDomainSet set -> (return . pure) (BuiltinDomainSet set)
