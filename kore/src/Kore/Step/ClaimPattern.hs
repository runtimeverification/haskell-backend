{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    , OnePathRule (..)
    , AllPathRule (..)
    , ReachabilityRule (..)
    , toSentence
    , applySubstitution
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Default as Default
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , Modality
    , SomeVariable
    , SomeVariableName (..)
    , TermLike
    , VariableName
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariable
    , RewritingVariableName
    , getRewritingVariable
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Verified as Verified

import Pretty
    ( Pretty (..)
    )
import qualified Pretty

-- | Representation of reachability claim types.
data ClaimPattern =
    ClaimPattern
    { left :: !(Pattern RewritingVariableName)
    , existentials :: ![ElementVariable RewritingVariableName]
    , right :: !(OrPattern RewritingVariableName)
    , attributes :: !(Attribute.Axiom Symbol RewritingVariableName)
    }
    deriving (Eq, Ord, Show, GHC.Generic)

instance NFData ClaimPattern

instance SOP.Generic ClaimPattern

instance SOP.HasDatatypeInfo ClaimPattern

instance Debug ClaimPattern

instance Diff ClaimPattern

instance From ClaimPattern Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes

instance From ClaimPattern Attribute.Label where
    from = Attribute.label . attributes

instance From ClaimPattern Attribute.RuleIndex where
    from = Attribute.identifier . attributes

instance Pretty ClaimPattern where
    pretty claimPattern'@(ClaimPattern _ _ _ _) =
        Pretty.vsep
            [ "left:"
            , Pretty.indent 4 (unparse left)
            , "existentials:"
            , Pretty.indent 4 (Pretty.list $ unparse <$> existentials)
            , "right:"
            , Pretty.indent 4 (unparse $ OrPattern.toTermLike right)
            ]
      where
        ClaimPattern
            { left
            , right
            , existentials
            } = claimPattern'

instance TopBottom ClaimPattern where
    isTop _ = False
    isBottom _ = False

instance From ClaimPattern Attribute.PriorityAttributes where
    from = from @(Attribute.Axiom _ _) . attributes

instance From ClaimPattern Attribute.HeatCool where
    from = from @(Attribute.Axiom _ _) . attributes

instance HasFreeVariables ClaimPattern RewritingVariableName where
    freeVariables claimPattern'@(ClaimPattern _ _ _ _) =
        freeVariables left
        <> freeVariables (OrPattern.toPattern right)
      where
        ClaimPattern { left, right } = claimPattern'

claimPatternToTerm
    :: Modality
    -> ClaimPattern
    -> TermLike VariableName
claimPatternToTerm modality representation@(ClaimPattern _ _ _ _) =
    TermLike.mkImplies
        leftPattern
        (TermLike.applyModality modality rightPattern)
  where
    ClaimPattern { left, right } = representation
    leftPattern =
        Pattern.toTermLike left
        & TermLike.mapVariables getRewritingVariable
    rightPattern =
        OrPattern.toTermLike right
        & TermLike.mapVariables getRewritingVariable

substituteRight
    :: Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName)
    -> ClaimPattern
    -> ClaimPattern
substituteRight subst claimPattern'@ClaimPattern { right, existentials } =
    claimPattern'
        { right = OrPattern.substitute subst' right
        }
  where
    subst' =
        foldr
            ( Map.delete
            . inject
            . TermLike.variableName
            )
            subst
            existentials

-- | Apply the substitution to the claim.
substitute
    :: Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName)
    -> ClaimPattern
    -> ClaimPattern
substitute subst claimPattern'@(ClaimPattern _ _ _ _) =
    substituteRight subst
    $ claimPattern'
        { left = Pattern.substitute subst left
        }
  where
    ClaimPattern { left, right, existentials } = claimPattern'

-- | Applies a substitution to a claim and checks that
-- it was fully applied, i.e. there is no substitution
-- variable left in the claim.
applySubstitution
    :: HasCallStack
    => Substitution RewritingVariableName
    -> ClaimPattern
    -> ClaimPattern
applySubstitution substitution claim =
    if finalClaim `isFreeOf` substitutedVariables
        then finalClaim
        else error
            (  "Substituted variables not removed from the rule, cannot throw "
            ++ "substitution away."
            )
  where
    subst = Substitution.toMap substitution
    finalClaim = substitute subst claim
    substitutedVariables = Substitution.variables substitution

-- |Is the rule free of the given variables?
isFreeOf
    :: ClaimPattern
    -> Set.Set (SomeVariable RewritingVariableName)
    -> Bool
isFreeOf rule =
    Set.disjoint
    $ FreeVariables.toSet
    $ freeVariables rule

-- | One-Path-Claim claim pattern.
newtype OnePathRule =
    OnePathRule { getOnePathRule :: ClaimPattern }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData OnePathRule

instance SOP.Generic OnePathRule

instance SOP.HasDatatypeInfo OnePathRule

instance Debug OnePathRule

instance Diff OnePathRule

-- | Converts a 'OnePathRule' into its term representation.
-- This is intended to be used only in unparsing situations,
-- as some of the variable information related to the
-- rewriting algorithm is lost.
onePathRuleToTerm :: OnePathRule -> TermLike VariableName
onePathRuleToTerm (OnePathRule claimPattern) =
    claimPatternToTerm TermLike.wEF claimPattern

instance Unparse OnePathRule where
    unparse claimPattern =
        "claim {}"
        <> Pretty.line'
        <> Pretty.nest 4
            (unparse $ onePathRuleToTerm claimPattern)
        <> Pretty.line'
        <> "[]"

    unparse2 claimPattern =
        "claim {}"
        Pretty.<+>
            unparse2 (onePathRuleToTerm claimPattern)
        Pretty.<+> "[]"

instance TopBottom OnePathRule where
    isTop _ = False
    isBottom _ = False

instance From OnePathRule Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes . getOnePathRule

instance From OnePathRule Attribute.Label where
    from = Attribute.label . attributes . getOnePathRule

instance From OnePathRule Attribute.RuleIndex where
    from = Attribute.identifier . attributes . getOnePathRule

instance From OnePathRule Attribute.Trusted where
    from = Attribute.trusted . attributes . getOnePathRule

-- | All-Path-Claim claim pattern.
newtype AllPathRule =
    AllPathRule { getAllPathRule :: ClaimPattern }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData AllPathRule

instance SOP.Generic AllPathRule

instance SOP.HasDatatypeInfo AllPathRule

instance Debug AllPathRule

instance Diff AllPathRule

instance Unparse AllPathRule where
    unparse claimPattern =
        "claim {}"
        <> Pretty.line'
        <> Pretty.nest 4
            (unparse $ allPathRuleToTerm claimPattern)
        <> Pretty.line'
        <> "[]"
    unparse2 claimPattern =
        "claim {}"
        Pretty.<+>
            unparse2 (allPathRuleToTerm claimPattern)
        Pretty.<+> "[]"

instance TopBottom AllPathRule where
    isTop _ = False
    isBottom _ = False

instance From AllPathRule Attribute.SourceLocation where
    from = Attribute.sourceLocation . attributes . getAllPathRule

instance From AllPathRule Attribute.Label where
    from = Attribute.label . attributes . getAllPathRule

instance From AllPathRule Attribute.RuleIndex where
    from = Attribute.identifier . attributes . getAllPathRule

instance From AllPathRule Attribute.Trusted where
    from = Attribute.trusted . attributes . getAllPathRule

-- | Converts a 'AllPathRule' into its term representation.
-- This is intended to be used only in unparsing situations,
-- as some of the variable information related to the
-- rewriting algorithm is lost.
allPathRuleToTerm :: AllPathRule -> TermLike VariableName
allPathRuleToTerm (AllPathRule claimPattern) =
    claimPatternToTerm TermLike.wAF claimPattern

-- | Unified One-Path and All-Path claim pattern.
data ReachabilityRule
    = OnePath !OnePathRule
    | AllPath !AllPathRule
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData ReachabilityRule

instance SOP.Generic ReachabilityRule

instance SOP.HasDatatypeInfo ReachabilityRule

instance Debug ReachabilityRule

instance Diff ReachabilityRule

instance Unparse ReachabilityRule where
    unparse (OnePath rule) = unparse rule
    unparse (AllPath rule) = unparse rule
    unparse2 (AllPath rule) = unparse2 rule
    unparse2 (OnePath rule) = unparse2 rule

instance TopBottom ReachabilityRule where
    isTop _ = False
    isBottom _ = False

instance Pretty ReachabilityRule where
    pretty (OnePath (OnePathRule rule)) =
        Pretty.vsep ["One-Path reachability rule:", Pretty.pretty rule]
    pretty (AllPath (AllPathRule rule)) =
        Pretty.vsep ["All-Path reachability rule:", Pretty.pretty rule]

instance From ReachabilityRule Attribute.SourceLocation where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.Label where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.RuleIndex where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

instance From ReachabilityRule Attribute.Trusted where
    from (OnePath onePathRule) = from onePathRule
    from (AllPath allPathRule) = from allPathRule

toSentence :: ReachabilityRule -> Verified.Sentence
toSentence rule =
    Syntax.SentenceClaimSentence $ Syntax.SentenceClaim Syntax.SentenceAxiom
        { sentenceAxiomParameters = []
        , sentenceAxiomPattern    = patt
        , sentenceAxiomAttributes = Default.def
        }
  where
    patt = case rule of
        OnePath rule' -> onePathRuleToTerm rule'
        AllPath rule' -> allPathRuleToTerm rule'
