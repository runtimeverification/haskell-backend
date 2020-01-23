{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnSimplificationWithRemainder
    ( WarnSimplificationWithRemainder (..)
    , Results (..)
    , Remainders (..)
    , warnSimplificationWithRemainder
    ) where

import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

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
import Pretty
    ( Pretty
    )
import qualified Pretty
import qualified SQL

{- | A log 'Entry' when a simplification rule has remainders.

We want to warn the user when a simplification rule has remainders because we
will skip the rule in that case.

 -}
data WarnSimplificationWithRemainder =
    WarnSimplificationWithRemainder
        { inputPattern :: TermLike Variable
        , sideCondition :: SideCondition Variable
        , results :: Results
        , remainders :: Remainders
        }
    deriving Typeable
    deriving (GHC.Generic)

newtype Results = Results { getResults :: OrPattern Variable }

instance Unparse Results where
    unparse = unparse . toTermLike . getResults
    unparse2 = unparse2 . toTermLike . getResults

instance SQL.Column Results where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

newtype Remainders = Remainders { getRemainders :: OrPattern Variable }

instance Unparse Remainders where
    unparse = unparse . toTermLike . getRemainders
    unparse2 = unparse2 . toTermLike . getRemainders

instance SQL.Column Remainders where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

toTermLike :: OrPattern Variable -> TermLike Variable
toTermLike = worker . OrPattern.toPatterns
  where
    worker =
        \case
            [ ] -> TermLike.mkBottom_
            [x] -> Pattern.toTermLike x
            (x : xs) -> TermLike.mkOr (Pattern.toTermLike x) (worker xs)

instance SOP.Generic WarnSimplificationWithRemainder

instance SOP.HasDatatypeInfo WarnSimplificationWithRemainder

instance SQL.Table WarnSimplificationWithRemainder where
    insertRow = SQL.insertRowGeneric
    selectRow = SQL.selectRowGeneric

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
    (Results . fmap (Pattern.mapVariables toVariable) -> results)
    (Remainders . fmap (Pattern.mapVariables toVariable) -> remainders)
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
                , Pretty.indent 2 (unparseOrPattern $ getResults results)
                , "remainders:"
                , Pretty.indent 2 (unparseOrPattern $ getRemainders remainders)
                ]
            , "Rule will be skipped."
            ]
      where
        WarnSimplificationWithRemainder { inputPattern, sideCondition } = entry
        WarnSimplificationWithRemainder { results, remainders } = entry
        unparseOrPattern = Pretty.vsep . map unparse . OrPattern.toPatterns
