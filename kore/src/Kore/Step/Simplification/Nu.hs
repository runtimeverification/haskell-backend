{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.Nu
    ( simplify
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( isSimplified
    , toTermLike
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , Nu (Nu)
    , SetVariable
    , mkNu
    )
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromMultiOr
    , fromTermLike
    )

{-|'simplify' simplifies a 'Nu' pattern with an 'OrPattern'
child.
-}
simplify
    :: InternalVariable variable
    => Nu variable (OrPattern variable)
    -> Simplifiable variable
simplify Nu { nuVariable, nuChild } =
    Simplifiable.fromMultiOr (makeEvaluate nuVariable <$> nuChild)

{-| evaluates a 'Nu' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: InternalVariable variable
    => SetVariable variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluate variable patt =
    Simplifiable.fromTermLike
    $ (if Pattern.isSimplified patt then TermLike.markSimplified else id)
    $ mkNu variable
    $ Pattern.toTermLike patt
