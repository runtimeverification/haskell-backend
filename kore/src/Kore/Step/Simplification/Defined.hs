{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Step.Simplification.Defined
    ( simplify
    ) where

import Prelude.Kore

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike


-- | Marks an 'OrPattern' resulted from simplification
-- as 'Defined'. Does not do any actual simplification.
simplify
    :: InternalVariable variable
    => Defined (OrPattern variable)
    -> OrPattern variable
simplify Defined { getDefined = defined } =
    OrPattern.fromTermLike
    $ markSimplified
    $ mkDefined
    $ OrPattern.toTermLike defined
