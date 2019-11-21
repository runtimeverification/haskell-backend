{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.Nu
    ( simplify
    ) where

import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    , isSimplified
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
    , SimplifiedChildren (SimplifiedChildren)
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromOrPattern
    )

{-|'simplify' simplifies a 'Nu' pattern with an 'OrPattern'
child.
-}
simplify
    :: InternalVariable variable
    => Nu variable (SimplifiedChildren variable)
    -> Simplifiable variable
simplify Nu { nuVariable, nuChild = SimplifiedChildren child } =
    Simplifiable.fromOrPattern (makeEvaluate nuVariable <$> child)

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
    $ (if Pattern.isSimplified patt then TermLike.markSimplified else id)
    $ mkNu variable
    $ Pattern.toTermLike patt
