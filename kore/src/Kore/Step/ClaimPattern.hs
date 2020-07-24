{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Debug
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( Modality
    , TermLike
    , VariableName
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariable
    , RewritingVariableName
    , getRewritingVariable
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )

import qualified Pretty

-- | Representation of reachability claim types.
data ClaimPattern =
    ClaimPattern
    { left :: !(Pattern RewritingVariableName)
    , existentials :: ![RewritingVariable]
    , right :: !(OrPattern RewritingVariableName)
    , attributes :: !(Attribute.Axiom Symbol RewritingVariableName)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance NFData ClaimPattern

instance SOP.Generic ClaimPattern

instance SOP.HasDatatypeInfo ClaimPattern

instance Debug ClaimPattern

instance Diff ClaimPattern

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

{-  | All-Path-Claim rule pattern.
-}
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

-- | Converts a 'OnePathRule' into its term representation.
-- This is intended to be used only in unparsing situations,
-- as some of the variable information related to the
-- rewriting algorithm is lost.
allPathRuleToTerm :: AllPathRule -> TermLike VariableName
allPathRuleToTerm (AllPathRule claimPattern) =
    claimPatternToTerm TermLike.wAF claimPattern
