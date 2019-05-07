{-|
Module      : Kore.Step.Simplification.Next
Description : Tools for Next pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Next
    ( simplify
    ) where

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Syntax.Next
import           Kore.Unparser

-- TODO: Move Next up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies a 'Next' pattern with an 'OrPattern'
child.

Right now this does not do any actual simplification.
-}
simplify
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Next Sort (OrPattern variable)
    -> OrPattern variable
simplify Next { nextChild = child } = simplifyEvaluated child

simplifyEvaluated
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => OrPattern variable
    -> OrPattern variable
simplifyEvaluated simplified =
    OrPattern.fromTermLike
    $ mkNext
    $ Pattern.toTermLike
    $ OrPattern.toPattern simplified
