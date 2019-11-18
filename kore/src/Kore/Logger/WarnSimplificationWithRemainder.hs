{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.WarnSimplificationWithRemainder
    ( WarnSimplificationWithRemainder (..)
    , warnSimplificationWithRemainder
    ) where

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified GHC.Stack as GHC

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import Kore.Logger
import Kore.Unparser

{- | A log 'Entry' when a simplification rule has remainders.

We want to warn the user when a simplification rule has remainders because we
will skip the rule in that case.

 -}
data WarnSimplificationWithRemainder =
    WarnSimplificationWithRemainder
        { inputPattern :: TermLike Variable
        , inputCondition :: Condition Variable
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
    -> Condition variable  -- ^ input condition
    -> OrPattern variable  -- ^ results
    -> OrPattern variable  -- ^ remainders
    -> logger ()
warnSimplificationWithRemainder
    (TermLike.mapVariables toVariable -> inputPattern)
    (Condition.mapVariables toVariable -> inputCondition)
    (fmap (Pattern.mapVariables toVariable) -> results)
    (fmap (Pattern.mapVariables toVariable) -> remainders)
  =
    logM WarnSimplificationWithRemainder
        { inputPattern
        , inputCondition
        , results
        , remainders
        }

instance Entry WarnSimplificationWithRemainder where
    entrySeverity _ = Warning

    entryScopes _ = mempty

    toLogMessage entry =
        LogMessage
            { message
            , severity = Warning
            , callstack = GHC.emptyCallStack
            }
      where
        WarnSimplificationWithRemainder { inputPattern, inputCondition } = entry
        WarnSimplificationWithRemainder { results, remainders } = entry
        unparseOrPattern = Pretty.vsep . map unparse . OrPattern.toPatterns
        message =
            (Pretty.renderStrict . layout . Pretty.vsep)
                [ "Simplification result with remainder:"
                , (Pretty.indent 2 . Pretty.vsep)
                    [ "input pattern:"
                    , Pretty.indent 2 (unparse inputPattern)
                    , "input condition:"
                    , Pretty.indent 2 (unparse inputCondition)
                    , "results:"
                    , Pretty.indent 2 (unparseOrPattern results)
                    , "remainders:"
                    , Pretty.indent 2 (unparseOrPattern remainders)
                    ]
                , "Rule will be skipped."
                ]
        layout = Pretty.layoutPretty Pretty.defaultLayoutOptions
