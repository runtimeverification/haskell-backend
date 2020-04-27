{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Rewriting.RewritingVariable
    ( RewritingVariable
    , getResultPattern
    , isConfigVariable
    , isRuleVariable
    , mkRewritingRule
    , unRewritingRule
    , mkRewritingPattern
    , getRemainderPredicate
    , getRemainderPattern
    , mkElementConfigVariable
    , mkElementRuleVariable
    ) where

import Prelude.Kore

import Data.Generics.Wrapped
    ( _Unwrapped
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , HasFreeVariables (..)
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Rewriting.UnifyingRule
import Kore.Unparser
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    , foldMapVariable
    )

newtype RewritingVariable =
    RewritingVariable { getRewritingVariable :: Target Variable }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving newtype FreshPartialOrd
    deriving newtype VariableName
    deriving newtype SubstitutionOrd
    deriving newtype Unparse

instance Hashable RewritingVariable

instance SOP.Generic RewritingVariable

instance SOP.HasDatatypeInfo RewritingVariable

instance Debug RewritingVariable

instance Diff RewritingVariable

instance From RewritingVariable Variable where
    from = from @_ @Variable . getRewritingVariable

instance From Variable RewritingVariable where
    from = RewritingVariable . from @Variable

instance SortedVariable RewritingVariable where
    lensVariableSort = _Unwrapped . lensVariableSort

instance FreshVariable RewritingVariable

getElementRewritingVariable
    :: ElementVariable RewritingVariable -> ElementVariable Variable
getElementRewritingVariable =
    Target.unTargetElement . fmap getRewritingVariable

getSetRewritingVariable
    :: SetVariable RewritingVariable -> SetVariable Variable
getSetRewritingVariable =
    Target.unTargetSet . fmap getRewritingVariable

getPatternRewritingVariable
    :: Pattern RewritingVariable
    -> Pattern Variable
getPatternRewritingVariable =
    Pattern.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable

isConfigVariable :: RewritingVariable -> Bool
isConfigVariable = Target.isNonTarget . getRewritingVariable

isRuleVariable :: RewritingVariable -> Bool
isRuleVariable = Target.isTarget . getRewritingVariable

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
getResultPattern :: Pattern RewritingVariable -> Pattern Variable
getResultPattern config@Conditional { substitution } =
    getPatternRewritingVariable
        config { Pattern.substitution = substitution' }
  where
    substitution' =
        Substitution.filter
            (foldMapVariable isConfigVariable)
            substitution

{- | Prepare a rule for unification or matching with the configuration.

The rule's variables are:

* marked with 'Target' so that they are preferred targets for substitution, and
* renamed to avoid any free variables from the configuration and side condition.

 -}
mkRewritingRule
    :: UnifyingRule rule
    => FreeVariables RewritingVariable
    -> rule Variable
    -> rule RewritingVariable
mkRewritingRule avoiding =
    snd
    . refreshRule avoiding
    . mapRuleVariables
        (fmap RewritingVariable . Target.mkElementTarget)
        (fmap RewritingVariable . Target.mkSetTarget)

{- | Unwrap the variables in a 'RulePattern'. Inverse of 'targetRuleVariables'.
 -}
unRewritingRule :: UnifyingRule rule => rule RewritingVariable -> rule Variable
unRewritingRule =
    mapRuleVariables
        (Target.unTargetElement . fmap getRewritingVariable)
        (Target.unTargetSet . fmap getRewritingVariable)

-- |Renames configuration variables to distinguish them from those in the rule.
mkRewritingPattern :: Pattern Variable -> Pattern RewritingVariable
mkRewritingPattern =
    Pattern.mapVariables
        (fmap RewritingVariable . Target.mkElementNonTarget)
        (fmap RewritingVariable . Target.mkSetNonTarget)

getRemainderPredicate :: Predicate RewritingVariable -> Predicate Variable
getRemainderPredicate predicate =
    Predicate.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable
        predicate
    & assert (all isUnifiedConfigVariable freeVars)
  where
    FreeVariables freeVars = freeVariables predicate

getRemainderPattern :: Pattern RewritingVariable -> Pattern Variable
getRemainderPattern pattern' =
    Pattern.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable
        pattern'
    & assert (all isUnifiedConfigVariable freeVars)
  where
    FreeVariables freeVars = freeVariables pattern'

isUnifiedConfigVariable :: UnifiedVariable RewritingVariable -> Bool
isUnifiedConfigVariable (ElemVar elemVar) =
    isConfigVariable (getElementVariable elemVar)
isUnifiedConfigVariable (SetVar setVar) =
    isConfigVariable (getSetVariable setVar)

mkElementConfigVariable
    :: ElementVariable Variable
    -> ElementVariable RewritingVariable
mkElementConfigVariable = fmap RewritingVariable . Target.mkElementNonTarget

mkElementRuleVariable
    :: ElementVariable Variable
    -> ElementVariable RewritingVariable
mkElementRuleVariable = fmap RewritingVariable . Target.mkElementTarget
