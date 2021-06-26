{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Internal.Substitute (
    Substitute (..),
    rename,
) where

import Data.Map.Strict (
    Map,
 )
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables,
 )
import Kore.Internal.TermLike.TermLike (
    TermLike,
    mkVar,
 )
import Kore.Internal.Variable
import qualified Kore.Substitute as Substitute
import Prelude.Kore

class
    (InternalVariable variable, HasFreeVariables child variable) =>
    Substitute variable child
        | child -> variable
    where
    substitute ::
        Map (SomeVariableName variable) (TermLike variable) ->
        child ->
        child

rename ::
    Substitute variable child =>
    Map (SomeVariableName variable) (SomeVariable variable) ->
    child ->
    child
rename = substitute . fmap mkVar
{-# INLINE rename #-}

instance
    InternalVariable variable =>
    Substitute variable (TermLike variable)
    where
    substitute = Substitute.substitute
    {-# INLINE substitute #-}
