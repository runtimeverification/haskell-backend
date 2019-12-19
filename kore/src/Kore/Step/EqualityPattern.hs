{-|
Description : Equality rules
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    , EqualityRule (..)
    , equalityPattern
    , equalityRuleToTerm
    , mapVariables
    ) where

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Default as Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    , SortedVariable
    )
import Kore.Step.Step
    ( UnifyingRule (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse
    , unparse
    , unparse2
    )
import qualified Kore.Variables.Fresh as Fresh

{- | Function axioms

 -}
data EqualityPattern variable = EqualityPattern
    { constraint :: !(Predicate variable)
    , eqLeft  :: !(TermLike.TermLike variable)
    , eqRight :: !(TermLike.TermLike variable)
    , attributes :: !Attribute.Axiom
    }
    deriving (GHC.Generic)

deriving instance Eq variable => Eq (EqualityPattern variable)
deriving instance Ord variable => Ord (EqualityPattern variable)
deriving instance Show variable => Show (EqualityPattern variable)

instance NFData variable => NFData (EqualityPattern variable)

instance SOP.Generic (EqualityPattern variable)

instance SOP.HasDatatypeInfo (EqualityPattern variable)

instance Debug variable => Debug (EqualityPattern variable)

instance (Debug variable, Diff variable) => Diff (EqualityPattern variable)

instance InternalVariable variable => Pretty (EqualityPattern variable) where
    pretty rulePattern'@(EqualityPattern _ _ _ _ ) =
        Pretty.vsep
            [ "constraint:"
            , Pretty.indent 4 (unparse constraint)
            , "eqLeft:"
            , Pretty.indent 4 (unparse eqLeft)
            , "eqRight:"
            , Pretty.indent 4 (unparse eqRight)
            ]
      where
        EqualityPattern
            { constraint
            , eqLeft
            , eqRight
            } = rulePattern'

instance TopBottom (EqualityPattern variable) where
    isTop _ = False
    isBottom _ = False

-- | Creates a basic, unconstrained, Equality pattern
equalityPattern
    :: InternalVariable variable
    => TermLike.TermLike variable
    -> TermLike.TermLike variable
    -> EqualityPattern variable
equalityPattern eqLeft eqRight =
    EqualityPattern
        { eqLeft
        , constraint = Predicate.makeTruePredicate_
        , eqRight
        , attributes = Default.def
        }

{-  | Equality-based rule pattern.
-}
newtype EqualityRule variable =
    EqualityRule { getEqualityRule :: EqualityPattern variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData variable => NFData (EqualityRule variable)

instance SOP.Generic (EqualityRule variable)

instance SOP.HasDatatypeInfo (EqualityRule variable)

instance Debug variable => Debug (EqualityRule variable)

instance (Debug variable, Diff variable) => Diff (EqualityRule variable)

instance
    InternalVariable variable
    => Unparse (EqualityRule variable)
  where
    unparse = unparse . equalityRuleToTerm
    unparse2 = unparse2 . equalityRuleToTerm


{-| Reverses an 'EqualityRule' back into its 'Pattern' representation.
  Should be the inverse of 'Rule.termToAxiomPattern'.
-}
equalityRuleToTerm
    :: Debug variable
    => Ord variable
    => Show variable
    => Unparse variable
    => SortedVariable variable
    => EqualityRule variable
    -> TermLike.TermLike variable
equalityRuleToTerm
     (EqualityRule
        (EqualityPattern
            Predicate.PredicateTrue
            left@(TermLike.Ceil_ _ resultSort1 _)
            (TermLike.Top_ resultSort2)
            _
        )
    )
  | resultSort1 == resultSort2 = left

equalityRuleToTerm
    (EqualityRule
        (EqualityPattern
            Predicate.PredicateTrue
            left
            right
            _
        )
    )
  =
    TermLike.mkEquals_ left right

equalityRuleToTerm
    (EqualityRule (EqualityPattern requires left right _))
  =
    TermLike.mkImplies
        (Predicate.unwrapPredicate requires)
        (TermLike.mkAnd (TermLike.mkEquals_ left right) TermLike.mkTop_)

instance UnifyingRule EqualityPattern where
    mapVariables mapping rule1@(EqualityPattern _ _ _ _) =
        rule1
            { constraint = Predicate.mapVariables mapping constraint
            , eqLeft = TermLike.mapVariables mapping eqLeft
            , eqRight = TermLike.mapVariables mapping eqRight
            }
      where
        EqualityPattern { constraint, eqLeft, eqRight } = rule1

    matchingPattern = eqLeft

    precondition = constraint

    refreshRule
        (FreeVariables.getFreeVariables -> avoid)
        rule1@(EqualityPattern _ _ _ _)
      =
        let rename = Fresh.refreshVariables avoid originalFreeVariables
            subst = TermLike.mkVar <$> rename
            eqLeft' = TermLike.substitute subst eqLeft
            constraint' = Predicate.substitute subst constraint
            eqRight' = TermLike.substitute subst eqRight
            rule2 =
                rule1
                    { eqLeft = eqLeft'
                    , constraint = constraint'
                    , eqRight = eqRight'
                    }
        in (rename, rule2)
      where
        EqualityPattern { eqLeft, constraint, eqRight } = rule1
        originalFreeVariables =
            FreeVariables.getFreeVariables
            $ freeVariables rule1

instance
    InternalVariable variable
    => HasFreeVariables (EqualityPattern variable) variable
  where
    freeVariables rule@(EqualityPattern _ _ _ _) = case rule of
        EqualityPattern { eqLeft, constraint, eqRight } ->
            freeVariables eqLeft
            <> freeVariables constraint
            <> freeVariables eqRight
