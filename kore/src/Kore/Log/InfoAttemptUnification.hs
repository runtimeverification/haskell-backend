{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.InfoAttemptUnification
    ( InfoAttemptUnification (..)
    , infoAttemptUnification
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , Variable
    , toVariable
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Unparser
    ( unparse
    )
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data InfoAttemptUnification =
    InfoAttemptUnification { term1, term2 :: !(TermLike Variable) }
    deriving (GHC.Generic)

instance SOP.Generic InfoAttemptUnification

instance SOP.HasDatatypeInfo InfoAttemptUnification

instance Entry InfoAttemptUnification where
    entrySeverity _ = Info

instance Pretty InfoAttemptUnification where
    pretty InfoAttemptUnification { term1, term2 } =
        Pretty.vsep
            [ "Attempting to unify"
            , Pretty.indent 4 $ unparse term1
            , Pretty.indent 2 "with"
            , Pretty.indent 4 $ unparse term2
            ]

infoAttemptUnification
    :: MonadLog log
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> log a
    -> log a
infoAttemptUnification term1' term2' =
    logWhile InfoAttemptUnification { term1, term2 }
  where
    mapVariables = TermLike.mapVariables (fmap toVariable) (fmap toVariable)
    term1 = mapVariables term1'
    term2 = mapVariables term2'
