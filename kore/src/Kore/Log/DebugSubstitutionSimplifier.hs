{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Log.DebugSubstitutionSimplifier
    ( DebugSubstitutionSimplifier (..)
    , whileDebugSubstitutionSimplifier
    , debugEvaluateConditionResult
    ) where

import Prelude.Kore

import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.OrCondition
    ( OrCondition (..)
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.SubstitutionSimplifier
import Kore.Internal.TermLike
import Kore.Unparser
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import SMT.SimpleSMT
    ( Result (..)
    )
import qualified SQL

data DebugSubstitutionSimplifier
    = WhileSimplifySubstitution 
    | SubstitutionSimplifierResult (OrCondition Variable)
    deriving (GHC.Generic)

instance SOP.Generic DebugSubstitutionSimplifier

instance SOP.HasDatatypeInfo DebugSubstitutionSimplifier


instance Pretty DebugSubstitutionSimplifier where
    pretty (WhileSimplifySubstitution) = "so pretty";
    {-
        (Pretty.vsep . concat)
        [ [ "evaluating predicate:" , Pretty.indent 4 (unparse predicate) ]
        , do
            sideCondition <- sideConditions
            [ "with side condition:", Pretty.indent 4 (unparse sideCondition) ]
        ]
      where
       predicate :| sideConditions = predicates
    -}
    pretty (SubstitutionSimplifierResult result) =
        "so pretty";
instance Entry DebugSubstitutionSimplifier where
    entrySeverity _ = Debug
    shortDoc _ = Just "while simplifying substitution"
    helpDoc _ = "log substitutions that we attempt to simplify"

--instance SQL.Table DebugSubstitutionSimplifier
{-
whileDebugSubstitutionSimplifier
    :: MonadLog log
    => InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log a
    -> log a
whileDebugSubstitutionSimplifier =
    logWhile . DebugSubstitutionSimplifier . fmap Predicate.externalizeFreshVariables
-}

debugSubstitutionSimplifierResult 
    :: MonadLog log 
    => InternalVariable variable 
    => OrCondition variable 
    -> log ()
debugSubstitutionSimplifierResult = logEntry . SubstitutionSimplifierResult . fmap TermLike.externalizeFreshVariables
