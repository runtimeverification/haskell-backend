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

import Prelude.Kore

import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute.Axiom
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
import Kore.Step.EqualityPattern
    ( EqualityRule (..)
    )
import qualified Kore.Step.EqualityPattern as EqualityPattern
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
        , remainders :: Remainders
        , rule :: EqualityRule Variable
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

instance SQL.Table WarnSimplificationWithRemainder

-- TODO (thomas.tuegel): Also get the rule which is being skipped.
{- | Log the @WarnSimplificationWithRemainder@ 'Entry'.
 -}
warnSimplificationWithRemainder
    :: MonadLog logger
    => InternalVariable variable
    => TermLike variable  -- ^ input pattern
    -> SideCondition variable  -- ^ input condition
    -> OrPattern variable  -- ^ remainders
    -> EqualityRule Variable
    -> logger ()
warnSimplificationWithRemainder
    (TermLike.mapVariables (fmap toVariable) (fmap toVariable) -> inputPattern)
    (SideCondition.mapVariables (fmap toVariable) (fmap toVariable)
        -> sideCondition
    )
    (Remainders . fmap (Pattern.mapVariables (fmap toVariable) (fmap toVariable))
        -> remainders
    )
    rule
  =
    logEntry WarnSimplificationWithRemainder
        { inputPattern
        , sideCondition
        , remainders
        , rule
        }

instance Entry WarnSimplificationWithRemainder where
    entrySeverity _ = Warning

instance Pretty WarnSimplificationWithRemainder where
    pretty entry =
        Pretty.vsep
            [ "Simplification result with non-empty remainder."
            , (Pretty.indent 2 . Pretty.vsep)
                [ "remainders:"
                , Pretty.indent 2 (unparseOrPattern $ getRemainders remainders)
                , "input condition:"
                , Pretty.indent 2 (unparse sideCondition)
                , "original source location of attempted rule:"
                , Pretty.indent 2 (Pretty.pretty location)
                , "input pattern:"
                , Pretty.indent 2 (unparse inputPattern)
                ]
            , "Rule will be skipped."
            ]
      where
        WarnSimplificationWithRemainder { inputPattern, sideCondition } = entry
        WarnSimplificationWithRemainder { remainders, rule } = entry
        unparseOrPattern = Pretty.vsep . map unparse . OrPattern.toPatterns
        location = Attribute.Axiom.sourceLocation . EqualityPattern.attributes . getEqualityRule $ rule
