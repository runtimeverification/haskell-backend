{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Log.DebugSubstitutionSimplifier
    ( DebugSubstitutionSimplifier (..)
    , whileDebugSubstitutionSimplifier
    , debugSubstitutionSimplifierResult
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

--import Kore.Unparser
import Data.Text
import Log

import Pretty
    ( Pretty (..)
    )
import qualified SQL

data DebugSubstitutionSimplifier
    = WhileSimplifySubstitution 
    | SubstitutionSimplifierResult Text
    deriving (GHC.Generic)

instance SOP.Generic DebugSubstitutionSimplifier

instance SOP.HasDatatypeInfo DebugSubstitutionSimplifier

instance Pretty DebugSubstitutionSimplifier where
    pretty (WhileSimplifySubstitution) = "Simplifying substitution.";
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
    pretty (SubstitutionSimplifierResult result) = pretty result;
instance Entry DebugSubstitutionSimplifier where
    entrySeverity _ = Debug
    shortDoc _ = Just "while simplifying substitution"
    helpDoc _ = "log substitutions that we attempt to simplify"

instance SQL.Table DebugSubstitutionSimplifier

whileDebugSubstitutionSimplifier
    :: MonadLog log
    => log a
    -> log a
whileDebugSubstitutionSimplifier =
    logWhile WhileSimplifySubstitution 

debugSubstitutionSimplifierResult 
    :: MonadLog log 
    => Text
    -> log ()
debugSubstitutionSimplifierResult = logEntry . SubstitutionSimplifierResult  
