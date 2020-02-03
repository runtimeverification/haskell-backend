{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.Nu
    ( simplify
    , makeEvaluate
    ) where

import Prelude.Kore

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    , simplifiedAttribute
    , toTermLike
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , Nu (Nu)
    , SetVariable
    , mkNu
    )
import qualified Kore.Internal.TermLike as TermLike
    ( setSimplified
    )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse

{-|'simplify' simplifies a 'Nu' pattern with an 'OrPattern'
child.
-}
simplify
    :: InternalVariable variable
    => Nu variable (OrPattern variable)
    -> OrPattern variable
simplify Nu { nuVariable, nuChild } = makeEvaluate nuVariable <$> nuChild

{-| evaluates a 'Nu' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: InternalVariable variable
    => SetVariable variable
    -> Pattern variable
    -> Pattern variable
makeEvaluate variable patt =
    Pattern.fromTermLike
    $ TermLike.setSimplified (Pattern.simplifiedAttribute patt)
    $ mkNu variable
    $ Pattern.toTermLike patt
