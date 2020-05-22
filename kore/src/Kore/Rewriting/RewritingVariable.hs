{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Rewriting.RewritingVariable
    ( RewritingVariable
    , isConfigVariable
    , isRuleVariable
    , mkConfigVariable
    , mkRuleVariable
    , mkElementConfigVariable
    , mkElementRuleVariable
    , mkUnifiedRuleVariable
    , mkUnifiedConfigVariable
    , mkRewritingRule
    , unRewritingRule
    , mkRewritingPattern
    , getResultPattern
    , getRemainderPredicate
    , getRemainderPattern
    ) where

import Prelude.Kore

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
import Kore.Internal.TermLike as TermLike hiding
    ( refreshVariables
    )
import Kore.Rewriting.UnifyingRule
import Kore.Unparser
import Kore.Variables.Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    , foldMapVariable
    )

data RewritingVariable
    = ConfigVariable !Variable
    | RuleVariable   !Variable
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance Hashable RewritingVariable

instance FreshPartialOrd RewritingVariable where
    infVariable =
        \case
            RuleVariable var   -> RuleVariable (infVariable var)
            ConfigVariable var -> ConfigVariable (infVariable var)
    {-# INLINE infVariable #-}

    supVariable =
        \case
            RuleVariable var   -> RuleVariable (supVariable var)
            ConfigVariable var -> ConfigVariable (supVariable var)
    {-# INLINE supVariable #-}

    nextVariable =
        \case
            RuleVariable var   -> RuleVariable (nextVariable var)
            ConfigVariable var -> ConfigVariable (nextVariable var)
    {-# INLINE nextVariable #-}

instance VariableName RewritingVariable

instance SubstitutionOrd RewritingVariable where
    compareSubstitution (RuleVariable _) (ConfigVariable _) = LT
    compareSubstitution (ConfigVariable _) (RuleVariable _) = GT
    compareSubstitution variable1 variable2 =
        on compareSubstitution (from @_ @Variable) variable1 variable2

instance Unparse RewritingVariable where
    unparse (ConfigVariable variable) = "Config" <> unparse variable
    unparse (RuleVariable variable) = "Rule" <> unparse variable

    unparse2 (ConfigVariable variable) = "Config" <> unparse2 variable
    unparse2 (RuleVariable variable) = "Rule" <> unparse2 variable

instance SOP.Generic RewritingVariable

instance SOP.HasDatatypeInfo RewritingVariable

instance Debug RewritingVariable

instance Diff RewritingVariable

instance From RewritingVariable Variable where
    from (ConfigVariable variable) = variable
    from (RuleVariable variable) = variable

instance From Variable RewritingVariable where
    from = RuleVariable

instance SortedVariable RewritingVariable where
    lensVariableSort f =
        \case
            ConfigVariable variable ->
                ConfigVariable <$> lensVariableSort f variable
            RuleVariable variable ->
                RuleVariable <$> lensVariableSort f variable
    {-# INLINE lensVariableSort #-}

instance FreshVariable RewritingVariable

mkElementConfigVariable
    :: ElementVariable Variable
    -> ElementVariable RewritingVariable
mkElementConfigVariable = fmap ConfigVariable

mkElementRuleVariable
    :: ElementVariable Variable
    -> ElementVariable RewritingVariable
mkElementRuleVariable = fmap RuleVariable

mkUnifiedRuleVariable
    :: UnifiedVariable Variable
    -> UnifiedVariable RewritingVariable
mkUnifiedRuleVariable (ElemVar var) = ElemVar (RuleVariable <$> var)
mkUnifiedRuleVariable (SetVar var) = SetVar (RuleVariable <$> var)

mkUnifiedConfigVariable
    :: UnifiedVariable Variable
    -> UnifiedVariable RewritingVariable
mkUnifiedConfigVariable (ElemVar var) = ElemVar (ConfigVariable <$> var)
mkUnifiedConfigVariable (SetVar var) = SetVar (ConfigVariable <$> var)

getRuleVariable :: RewritingVariable -> Maybe Variable
getRuleVariable (RuleVariable var) = Just var
getRuleVariable _ = Nothing

getUnifiedRuleVariable
    :: UnifiedVariable RewritingVariable
    -> Maybe (UnifiedVariable Variable)
getUnifiedRuleVariable (ElemVar var) = ElemVar <$> traverse getRuleVariable var
getUnifiedRuleVariable (SetVar var) = SetVar <$> traverse getRuleVariable var

getElementRewritingVariable
    :: ElementVariable RewritingVariable -> ElementVariable Variable
getElementRewritingVariable = fmap (from @_ @Variable)

getSetRewritingVariable
    :: SetVariable RewritingVariable -> SetVariable Variable
getSetRewritingVariable = fmap (from @_ @Variable)

getPattern
    :: HasCallStack
    => Pattern RewritingVariable
    -> Pattern Variable
getPattern pattern' =
    getPatternAux pattern'
    & assert (all isUnifiedConfigVariable freeVars)
  where
    freeVars = freeVariables pattern' & FreeVariables.toList

getPatternAux
    :: Pattern RewritingVariable
    -> Pattern Variable
getPatternAux pattern' =
    Pattern.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable
        pattern'

mkConfigVariable :: Variable -> RewritingVariable
mkConfigVariable = ConfigVariable

mkRuleVariable :: Variable -> RewritingVariable
mkRuleVariable = RuleVariable

isConfigVariable :: RewritingVariable -> Bool
isConfigVariable (ConfigVariable _) = True
isConfigVariable _ = False

isRuleVariable :: RewritingVariable -> Bool
isRuleVariable (RuleVariable _) = True
isRuleVariable _ = False

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
getResultPattern
    :: HasCallStack
    => FreeVariables RewritingVariable
    -> Pattern RewritingVariable
    -> Pattern Variable
getResultPattern initial config@Conditional { substitution } =
    getPatternAux renamed
  where
    substitution' =
        Substitution.filter
            (foldMapVariable isConfigVariable)
            substitution
    filtered = config { Pattern.substitution = substitution' }
    avoiding =
        initial
        & FreeVariables.toSet
        & Set.map (from @_ @(UnifiedVariable Variable))
    introduced =
        Set.fromAscList
        . mapMaybe getUnifiedRuleVariable
        . Set.toAscList
        . FreeVariables.toSet
        $ freeVariables filtered
    renaming =
        Map.mapKeys mkUnifiedRuleVariable
        . Map.map (TermLike.mkVar . mkUnifiedConfigVariable)
        $ refreshVariables avoiding introduced
    renamed :: Pattern RewritingVariable
    renamed =
        filtered
            { term = TermLike.substitute renaming (term filtered)
            , predicate = Predicate.substitute renaming (predicate filtered)
            }

{- | Prepare a rule for unification or matching with the configuration.

The rule's variables are:

* marked with 'Target' so that they are preferred targets for substitution, and
* renamed to avoid any free variables from the configuration and side condition.

 -}
mkRewritingRule
    :: UnifyingRule rule
    => rule Variable
    -> rule RewritingVariable
mkRewritingRule = mapRuleVariables (fmap RuleVariable) (fmap RuleVariable)

{- | Unwrap the variables in a 'RulePattern'. Inverse of 'targetRuleVariables'.
 -}
unRewritingRule :: UnifyingRule rule => rule RewritingVariable -> rule Variable
unRewritingRule =
    mapRuleVariables getElementRewritingVariable getSetRewritingVariable

-- |Renames configuration variables to distinguish them from those in the rule.
mkRewritingPattern :: Pattern Variable -> Pattern RewritingVariable
mkRewritingPattern =
    Pattern.mapVariables
        (fmap ConfigVariable)
        (fmap ConfigVariable)

getRemainderPredicate :: Predicate RewritingVariable -> Predicate Variable
getRemainderPredicate predicate =
    Predicate.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable
        predicate
    & assert (all isUnifiedConfigVariable freeVars)
  where
    freeVars = freeVariables predicate & FreeVariables.toList

getRemainderPattern
    :: HasCallStack
    => Pattern RewritingVariable
    -> Pattern Variable
getRemainderPattern = getPattern

isUnifiedConfigVariable :: UnifiedVariable RewritingVariable -> Bool
isUnifiedConfigVariable (ElemVar elemVar) =
    isConfigVariable (getElementVariable elemVar)
isUnifiedConfigVariable (SetVar setVar) =
    isConfigVariable (getSetVariable setVar)
