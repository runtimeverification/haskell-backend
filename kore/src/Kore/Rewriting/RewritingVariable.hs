{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , RewritingVariable
    , isConfigVariable
    , isRuleVariable
    , isSomeConfigVariable
    , isSomeConfigVariableName
    , isSomeRuleVariable
    , isSomeRuleVariableName
    , isElementRuleVariable
    , isElementRuleVariableName
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

import Control.DeepSeq
    ( NFData
    )
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

{- | The name of a 'RewritingVariable'.
 -}
data RewritingVariableName
    = ConfigVariableName !VariableName
    | RuleVariableName   !VariableName
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance Hashable RewritingVariableName

instance NFData RewritingVariableName

instance SOP.Generic RewritingVariableName

instance SOP.HasDatatypeInfo RewritingVariableName

instance Debug RewritingVariableName

instance Diff RewritingVariableName

instance SubstitutionOrd RewritingVariableName where
    compareSubstitution (RuleVariableName _) (ConfigVariableName _) = LT
    compareSubstitution (ConfigVariableName _) (RuleVariableName _) = GT
    compareSubstitution variable1 variable2 =
        on compareSubstitution toVariableName variable1 variable2

instance FreshPartialOrd RewritingVariableName where
    minBoundName =
        \case
            RuleVariableName var   -> RuleVariableName (minBoundName var)
            ConfigVariableName var -> ConfigVariableName (minBoundName var)
    {-# INLINE minBoundName #-}

    maxBoundName =
        \case
            RuleVariableName var   -> RuleVariableName (maxBoundName var)
            ConfigVariableName var -> ConfigVariableName (maxBoundName var)
    {-# INLINE maxBoundName #-}

    nextName (RuleVariableName name1) (RuleVariableName name2) =
        RuleVariableName <$> nextName name1 name2
    nextName (ConfigVariableName name1) (ConfigVariableName name2) =
        ConfigVariableName <$> nextName name1 name2
    nextName _ _ = Nothing
    {-# INLINE nextName #-}

instance Unparse RewritingVariableName where
    unparse (ConfigVariableName variable) = "Config" <> unparse variable
    unparse (RuleVariableName variable) = "Rule" <> unparse variable

    unparse2 (ConfigVariableName variable) = "Config" <> unparse2 variable
    unparse2 (RuleVariableName variable) = "Rule" <> unparse2 variable

instance From RewritingVariableName VariableName where
    from (ConfigVariableName variable) = variable
    from (RuleVariableName variable) = variable

instance From VariableName RewritingVariableName where
    from = RuleVariableName

instance FreshName RewritingVariableName

type RewritingVariable = Variable RewritingVariableName

mkElementConfigVariable
    :: ElementVariable VariableName
    -> ElementVariable RewritingVariableName
mkElementConfigVariable = (fmap . fmap) ConfigVariableName

mkElementRuleVariable
    :: ElementVariable VariableName
    -> ElementVariable RewritingVariableName
mkElementRuleVariable = (fmap . fmap) RuleVariableName

mkUnifiedRuleVariable
    :: SomeVariable VariableName
    -> SomeVariable RewritingVariableName
mkUnifiedRuleVariable = (fmap . fmap) RuleVariableName

mkUnifiedConfigVariable
    :: SomeVariable VariableName
    -> SomeVariable RewritingVariableName
mkUnifiedConfigVariable = (fmap . fmap) ConfigVariableName

getRuleVariable :: RewritingVariableName -> Maybe VariableName
getRuleVariable (RuleVariableName var) = Just var
getRuleVariable _ = Nothing

getUnifiedRuleVariable
    :: SomeVariable RewritingVariableName
    -> Maybe (SomeVariable VariableName)
getUnifiedRuleVariable = (traverse . traverse) getRuleVariable

getPattern
    :: HasCallStack
    => Pattern RewritingVariableName
    -> Pattern VariableName
getPattern pattern' =
    getPatternAux pattern'
    & assert (all isSomeConfigVariable freeVars)
  where
    freeVars = freeVariables pattern' & FreeVariables.toList

getRewritingVariable
    :: AdjSomeVariableName (RewritingVariableName -> VariableName)
getRewritingVariable = pure (from @RewritingVariableName @VariableName)

getPatternAux :: Pattern RewritingVariableName -> Pattern VariableName
getPatternAux = Pattern.mapVariables getRewritingVariable

mkConfigVariable :: VariableName -> RewritingVariableName
mkConfigVariable = ConfigVariableName

mkRuleVariable :: VariableName -> RewritingVariableName
mkRuleVariable = RuleVariableName

isConfigVariable :: RewritingVariableName -> Bool
isConfigVariable (ConfigVariableName _) = True
isConfigVariable _ = False

isRuleVariable :: RewritingVariableName -> Bool
isRuleVariable (RuleVariableName _) = True
isRuleVariable _ = False

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
getResultPattern
    :: HasCallStack
    => FreeVariables RewritingVariableName
    -> Pattern RewritingVariableName
    -> Pattern VariableName
getResultPattern initial config@Conditional { substitution } =
    getPatternAux renamed
  where
    substitution' = Substitution.filter isSomeConfigVariable substitution
    filtered = config { Pattern.substitution = substitution' }
    avoiding =
        initial
        & FreeVariables.toNames
        & (Set.map . fmap) toVariableName
    introduced =
        Set.fromAscList
        . mapMaybe getUnifiedRuleVariable
        . Set.toAscList
        . FreeVariables.toSet
        $ freeVariables filtered
    renaming =
        Map.mapKeys (fmap RuleVariableName)
        . Map.map (TermLike.mkVar . mkUnifiedConfigVariable)
        $ refreshVariables avoiding introduced
    renamed :: Pattern RewritingVariableName
    renamed = filtered & Pattern.substitute renaming

{- | Prepare a rule for unification or matching with the configuration.

The rule's variables are:

* marked with 'Target' so that they are preferred targets for substitution, and
* renamed to avoid any free variables from the configuration and side condition.

 -}
mkRewritingRule
    :: UnifyingRule rule
    => rule VariableName
    -> rule RewritingVariableName
mkRewritingRule = mapRuleVariables (pure RuleVariableName)

{- | Unwrap the variables in a 'RulePattern'. Inverse of 'targetRuleVariables'.
 -}
unRewritingRule
    :: UnifyingRule rule
    => rule RewritingVariableName
    -> rule VariableName
unRewritingRule = mapRuleVariables getRewritingVariable

-- |Renames configuration variables to distinguish them from those in the rule.
mkRewritingPattern :: Pattern VariableName -> Pattern RewritingVariableName
mkRewritingPattern = Pattern.mapVariables (pure ConfigVariableName)

getRemainderPredicate
    :: Predicate RewritingVariableName
    -> Predicate VariableName
getRemainderPredicate predicate =
    Predicate.mapVariables getRewritingVariable predicate
    & assert (all isSomeConfigVariable freeVars)
  where
    freeVars = freeVariables predicate & FreeVariables.toList

getRemainderPattern
    :: HasCallStack
    => Pattern RewritingVariableName
    -> Pattern VariableName
getRemainderPattern = getPattern

isSomeConfigVariable :: SomeVariable RewritingVariableName -> Bool
isSomeConfigVariable = isSomeConfigVariableName . variableName

isSomeConfigVariableName :: SomeVariableName RewritingVariableName -> Bool
isSomeConfigVariableName = foldSomeVariableName (pure isConfigVariable)

isSomeRuleVariable :: SomeVariable RewritingVariableName -> Bool
isSomeRuleVariable = isSomeRuleVariableName . variableName

isSomeRuleVariableName :: SomeVariableName RewritingVariableName -> Bool
isSomeRuleVariableName = foldSomeVariableName (pure isRuleVariable)

isElementRuleVariable :: ElementVariable RewritingVariableName -> Bool
isElementRuleVariable = isElementRuleVariableName . variableName

isElementRuleVariableName :: ElementVariableName RewritingVariableName -> Bool
isElementRuleVariableName = any isRuleVariable
