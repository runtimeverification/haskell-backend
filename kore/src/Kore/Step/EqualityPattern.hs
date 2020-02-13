{-|
Description : Equality rules
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.EqualityPattern
    ( EqualityRule (..)
    , equalityPattern
    , equalityRuleToTerm
    , isSimplificationRule
    , getPriorityOfRule
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Default as Default
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Owise as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
    ( Symbol (..)
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Step.Step
    ( UnifyingRule (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Variables.Fresh as Fresh
import qualified SQL

{- | Function axioms

 -}
data EqualityRule variable = EqualityRule
    { requires :: !(Predicate variable)
    , left  :: !(TermLike.TermLike variable)
    , right :: !(TermLike.TermLike variable)
    , ensures :: !(Predicate variable)
    , attributes :: !(Attribute.Axiom Symbol)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance NFData variable => NFData (EqualityRule variable)

instance SOP.Generic (EqualityRule variable)

instance SOP.HasDatatypeInfo (EqualityRule variable)

instance Debug variable => Debug (EqualityRule variable)

instance (Debug variable, Diff variable) => Diff (EqualityRule variable)

instance InternalVariable variable => Unparse (EqualityRule variable) where
    unparse = unparse . from @_ @(TermLike variable)
    unparse2 = unparse2 . from @_ @(TermLike variable)

instance InternalVariable variable => Pretty (EqualityRule variable) where
    pretty rulePattern'@(EqualityRule _ _ _ _ _) =
        Pretty.vsep
            [ "requires:"
            , Pretty.indent 4 (unparse requires)
            , "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        EqualityRule
            { requires
            , left
            , right
            , ensures
            } = rulePattern'

instance TopBottom (EqualityRule variable) where
    isTop _ = False
    isBottom _ = False

instance
    (InternalVariable variable, Typeable variable)
    => SQL.Table (EqualityRule variable)

instance
    (InternalVariable variable, Typeable variable)
    => SQL.Column (EqualityRule variable)
  where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

-- | Creates a basic, unconstrained, Equality pattern
equalityPattern
    :: InternalVariable variable
    => TermLike.TermLike variable
    -> TermLike.TermLike variable
    -> EqualityRule variable
equalityPattern left right =
    EqualityRule
        { left
        , requires = Predicate.makeTruePredicate_
        , right
        , ensures = Predicate.makeTruePredicate_
        , attributes = Default.def
        }

instance
    InternalVariable variable
    => From (EqualityRule variable) (TermLike variable)
  where
    from equalityRule@(EqualityRule _ _ _ _ _)
      | Predicate.PredicateTrue <- requires
      , Predicate.PredicateTrue <- ensures
      , TermLike.Ceil_ _ resultSort1 _ <- left
      , TermLike.Top_ resultSort2 <- right
      , resultSort1 == resultSort2
      = left

      | Predicate.PredicateTrue <- requires
      , Predicate.PredicateTrue <- ensures
      = TermLike.mkEquals_ left right

      | otherwise =
        TermLike.mkImplies
            (Predicate.unwrapPredicate requires)
            (TermLike.mkAnd
                (TermLike.mkEquals_ left right)
                (Predicate.unwrapPredicate ensures)
            )

      where
        EqualityRule { left, requires, right, ensures } = equalityRule

{- | Reverses an 'EqualityRule' back into its 'Pattern' representation.

The inverse of 'Rule.termToAxiomPattern'.

-}
equalityRuleToTerm
    :: InternalVariable variable
    => EqualityRule variable
    -> TermLike.TermLike variable
equalityRuleToTerm = from

instance UnifyingRule EqualityRule where
    mapRuleVariables mapElemVar mapSetVar rule1@(EqualityRule _ _ _ _ _) =
        rule1
            { requires = mapPredicateVariables requires
            , left = mapTermLikeVariables left
            , right = mapTermLikeVariables right
            , ensures = mapPredicateVariables ensures
            }
      where
        EqualityRule { requires, left, right, ensures } = rule1
        mapTermLikeVariables = TermLike.mapVariables mapElemVar mapSetVar
        mapPredicateVariables = Predicate.mapVariables mapElemVar mapSetVar

    matchingPattern = left

    precondition = requires

    refreshRule
        (FreeVariables.getFreeVariables -> avoid)
        rule1@(EqualityRule _ _ _ _ _)
      =
        let rename = Fresh.refreshVariables avoid originalFreeVariables
            subst = TermLike.mkVar <$> rename
            left' = TermLike.substitute subst left
            requires' = Predicate.substitute subst requires
            right' = TermLike.substitute subst right
            ensures' = Predicate.substitute subst ensures
            rule2 =
                rule1
                    { left = left'
                    , requires = requires'
                    , right = right'
                    , ensures = ensures'
                    }
        in (rename, rule2)
      where
        EqualityRule { left, requires, right, ensures } = rule1
        originalFreeVariables =
            FreeVariables.getFreeVariables
            $ freeVariables rule1

instance
    InternalVariable variable
    => HasFreeVariables (EqualityRule variable) variable
  where
    freeVariables rule@(EqualityRule _ _ _ _ _) = case rule of
        EqualityRule { left, requires, right, ensures } ->
            freeVariables left
            <> freeVariables requires
            <> freeVariables right
            <> freeVariables ensures

isSimplificationRule :: EqualityRule variable -> Bool
isSimplificationRule EqualityRule { attributes } =
    isSimplification
  where
    Attribute.Simplification { isSimplification } =
        Attribute.simplification attributes

getPriorityOfRule :: EqualityRule variable -> Integer
getPriorityOfRule EqualityRule { attributes } =
    if isOwise
        then 200
        else fromMaybe 100 getPriority
  where
    Attribute.Priority { getPriority } =
        Attribute.priority attributes
    Attribute.Owise { isOwise } =
        Attribute.owise attributes
