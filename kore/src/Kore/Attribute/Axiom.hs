{-|
Module      : Kore.Attribute.Axiom
Description : Axiom sentence attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Attribute.Axiom
    ( Axiom (..)
    , lensHeatCool, HeatCool (..)
    , lensProductionID, ProductionID (..)
    , lensAssoc, Assoc (..)
    , lensComm, Comm (..)
    , lensUnit, Unit (..)
    , lensIdem, Idem (..)
    , lensTrusted, Trusted (..)
    , lensConcrete, Concrete (..)
    , lensSimplification, Simplification (..)
    , lensOverload, Overload (..)
    , lensSmtLemma, SmtLemma (..)
    , lensLabel, Label (..)
    , lensSourceLocation, SourceLocation (..)
    , lensConstructor, Constructor (..)
    , lensIdentifier, RuleIndex (..)
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
                 ( Default (..) )
import           GHC.Generics
                 ( Generic )

import qualified Control.Lens.TH.Rules as Lens
import           Kore.Attribute.Assoc
import           Kore.Attribute.Axiom.Concrete
import           Kore.Attribute.Axiom.Constructor
import           Kore.Attribute.Axiom.Unit
import           Kore.Attribute.Comm
import           Kore.Attribute.HeatCool
import           Kore.Attribute.Idem
import           Kore.Attribute.Label
import           Kore.Attribute.Overload
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Attribute.ProductionID
import           Kore.Attribute.RuleIndex
import           Kore.Attribute.Simplification
import           Kore.Attribute.SmtLemma
import           Kore.Attribute.SourceLocation
import           Kore.Attribute.Trusted

{- | Attributes specific to Kore axiom sentences.
 -}
data Axiom =
    Axiom
    { heatCool :: !HeatCool
    -- ^ An axiom may be denoted as a heating or cooling rule.
    , productionID :: !ProductionID
    -- ^ The identifier from the front-end identifying a rule or group of rules.
    , assoc :: !Assoc
    -- ^ The axiom is an associativity axiom.
    , comm :: !Comm
    -- ^ The axiom is a commutativity axiom.
    , unit :: !Unit
    -- ^ The axiom is a left- or right-unit axiom.
    , idem :: !Idem
    -- ^ The axiom is an idempotency axiom.
    , trusted :: !Trusted
    -- ^ The claim is trusted
    , concrete :: !Concrete
    , simplification :: !Simplification
    -- ^ This is an axiom used for simplification
    -- (as opposed to, e.g., function evaluation).
    , overload :: !Overload
    -- ^ The axiom is an overloaded-production axiom.
    , smtLemma :: !SmtLemma
    -- ^ The axiom should be sent to SMT as a lemma.
    , label :: !Label
    -- ^ The user-defined label associated with the axiom.
    , sourceLocation :: !SourceLocation
    -- ^ Source and location in the original file.
    , constructor :: !Constructor
    -- ^ Shows that this is one of the constructor axioms
    -- (e.g. no confusion, no junk)
    , identifier :: !RuleIndex
    -- ^ Used to identify an axiom in the repl.
    } deriving (Eq, Ord, Show, Generic)

instance NFData Axiom

Lens.makeLenses ''Axiom

instance Default Axiom where
    def =
        Axiom
            { heatCool = def
            , productionID = def
            , assoc = def
            , comm = def
            , unit = def
            , idem = def
            , trusted = def
            , concrete = def
            , simplification = def
            , overload = def
            , smtLemma = def
            , label = def
            , sourceLocation = def
            , constructor = def
            , identifier = def
            }

instance ParseAttributes Axiom where
    parseAttribute attr =
        lensHeatCool (parseAttribute attr)
        Monad.>=> lensProductionID (parseAttribute attr)
        Monad.>=> lensAssoc (parseAttribute attr)
        Monad.>=> lensComm (parseAttribute attr)
        Monad.>=> lensUnit (parseAttribute attr)
        Monad.>=> lensIdem (parseAttribute attr)
        Monad.>=> lensTrusted (parseAttribute attr)
        Monad.>=> lensConcrete (parseAttribute attr)
        Monad.>=> lensSimplification (parseAttribute attr)
        Monad.>=> lensOverload (parseAttribute attr)
        Monad.>=> lensSmtLemma (parseAttribute attr)
        Monad.>=> lensLabel (parseAttribute attr)
        Monad.>=> lensSourceLocation (parseAttribute attr)
        Monad.>=> lensConstructor (parseAttribute attr)
