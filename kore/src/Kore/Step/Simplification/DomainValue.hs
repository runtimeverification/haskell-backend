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

import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Step.Conditional
                 ( Conditional )
import           Kore.Step.OrPattern
                 ( OrPattern )
import           Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.Syntax
import           Kore.Unparser

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => SmtMetadataTools attrs
    -> Domain.Builtin (OrPattern variable)
    -> OrPattern variable
simplify _ builtin =
    MultiOr.filterOr $ do
        child <- simplifyBuiltin builtin
        return (mkDomainValue <$> child)

simplifyBuiltin
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => Domain.Builtin (OrPattern variable)
    -> MultiOr (Conditional variable (Domain.Builtin (TermLike variable)))
simplifyBuiltin =
    \case
        Domain.BuiltinExternal _ext -> do
            _ext <- sequence _ext
            return (Domain.BuiltinExternal <$> sequenceA _ext)
        Domain.BuiltinMap _map -> do
            _map <- sequence _map
            -- MultiOr propagates \bottom children upward.
            return (Domain.BuiltinMap <$> sequenceA _map)
        Domain.BuiltinList _list -> do
            _list <- sequence _list
            -- MultiOr propagates \bottom children upward.
            return (Domain.BuiltinList <$> sequenceA _list)
        Domain.BuiltinSet set -> (return . pure) (Domain.BuiltinSet set)
        Domain.BuiltinInt int -> (return . pure) (Domain.BuiltinInt int)
        Domain.BuiltinBool bool -> (return . pure) (Domain.BuiltinBool bool)
