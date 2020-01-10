{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Logger.WarnRemoveDestinationUnification
    ( WarnRemoveDestinationUnification (..)
    , warnRemoveDestinationUnification
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )

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
import Kore.Logger
import Kore.Unification.Error
    ( UnificationOrSubstitutionError
    )
import Kore.Unparser

{- | A log 'Entry' when a simplification rule has remainders.

We want to warn the user when a simplification rule has remainders because we
will skip the rule in that case.

 -}
data WarnRemoveDestinationUnification =
    WarnRemoveDestinationUnification
        { configTerm :: TermLike Variable
        , destTerm :: TermLike Variable
        , sideCondition :: SideCondition Variable
        , unificationError :: UnificationOrSubstitutionError
        }
    deriving Typeable

{- | Log the @WarnRemoveDestinationUnification@ 'Entry'.
 -}
warnRemoveDestinationUnification
    :: MonadLog logger
    => InternalVariable variable
    => TermLike variable  -- ^ config pattern
    -> TermLike variable  -- ^ destination pattern
    -> SideCondition variable  -- ^ config condition
    -> UnificationOrSubstitutionError
    -> logger ()
warnRemoveDestinationUnification
    (TermLike.mapVariables toVariable -> configTerm)
    (TermLike.mapVariables toVariable -> destTerm)
    (SideCondition.mapVariables toVariable -> sideCondition)
    unificationError
  =
    logM WarnRemoveDestinationUnification
        { configTerm
        , destTerm
        , sideCondition
        , unificationError
        }

instance Entry WarnRemoveDestinationUnification where
    entrySeverity _ = Warning

instance Pretty WarnRemoveDestinationUnification where
    pretty entry =
        Pretty.vsep
            [ "Unification error in removeDestination:"
            , (Pretty.indent 2 . Pretty.vsep)
                [ "config pattern:"
                , Pretty.indent 2 (unparse configTerm)
                , "input condition:"
                , Pretty.indent 2 (unparse sideCondition)
                , "destination pattern:"
                , Pretty.indent 2 (unparse destTerm)
                , "unification error:"
                , Pretty.indent 2 (Pretty.pretty unificationError)
                ]
            , "Destination will not be removed."
            ]
      where
        WarnRemoveDestinationUnification { configTerm, sideCondition } = entry
        WarnRemoveDestinationUnification { destTerm, unificationError } = entry
