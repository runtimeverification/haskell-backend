{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnSimplificationWithRemainder
    ( WarnSimplificationWithRemainder (..)
    , warnSimplificationWithRemainder
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( mapVariables
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import Kore.Unparser
import Log

{- | A log 'Entry' when a simplification rule has remainders.

We want to warn the user when a simplification rule has remainders because we
will skip the rule in that case.

 -}
data WarnSimplificationWithRemainder =
    WarnSimplificationWithRemainder
        { inputPattern :: TermLike Variable
        , sideCondition :: SideCondition Variable
        , results :: OrPattern Variable
        , remainders :: OrPattern Variable
        }
    deriving Typeable

-- TODO (thomas.tuegel): Also get the rule which is being skipped.
{- | Log the @WarnSimplificationWithRemainder@ 'Entry'.
 -}
warnSimplificationWithRemainder
    :: MonadLog logger
    => InternalVariable variable
    => TermLike variable  -- ^ input pattern
    -> SideCondition variable  -- ^ input condition
    -> OrPattern variable  -- ^ results
    -> OrPattern variable  -- ^ remainders
    -> logger ()
warnSimplificationWithRemainder
    (TermLike.mapVariables toVariable -> inputPattern)
    (SideCondition.mapVariables toVariable -> sideCondition)
    (fmap (Pattern.mapVariables toVariable) -> results)
    (fmap (Pattern.mapVariables toVariable) -> remainders)
  =
    logM WarnSimplificationWithRemainder
        { inputPattern
        , sideCondition
        , results
        , remainders
        }

instance Entry WarnSimplificationWithRemainder where
    entrySeverity _ = Warning

instance Pretty WarnSimplificationWithRemainder where
    pretty entry =
        Pretty.vsep
            [ "Simplification result with remainder:"
            , (Pretty.indent 2 . Pretty.vsep)
                [ "input pattern:"
                , Pretty.indent 2 (unparse inputPattern)
                , "input condition:"
                , Pretty.indent 2 (unparse sideCondition)
                , "results:"
                , Pretty.indent 2 (unparseOrPattern results)
                , "remainders:"
                , Pretty.indent 2 (unparseOrPattern remainders)
                ]
            , "Rule will be skipped."
            ]
      where
        WarnSimplificationWithRemainder { inputPattern, sideCondition } = entry
        WarnSimplificationWithRemainder { results, remainders } = entry
        unparseOrPattern = Pretty.vsep . map unparse . OrPattern.toPatterns
