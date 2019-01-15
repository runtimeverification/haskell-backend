{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Test.Kore.Comparators
Description : Declares various data types involved in testing as instances of
              the 'EqualWithExplanation' class.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Test.Kore.Comparators where

import Control.Applicative
       ( Alternative (..) )
import Control.Comonad.Trans.Cofree
       ( CofreeF (..), CofreeT (..) )
import Data.Functor.Classes
import Data.Functor.Identity
       ( Identity (..) )
import Numeric.Natural
       ( Natural )

import qualified Kore.Annotation.Null as Annotation
import           Kore.Annotation.Valid
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.OnePath.Step
                 ( StrategyPattern )
import           Kore.OnePath.Step as StrategyPattern
                 ( StrategyPattern (..) )
import           Kore.Predicate.Predicate
import           Kore.Proof.Functional
import           Kore.Step.BaseStep
import           Kore.Step.BaseStep as StepResult
                 ( StepResult (..) )
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.OrOfExpandedPattern
import           Kore.Step.Pattern
import qualified Kore.Step.PatternAttributesError as PatternAttributesError
import           Kore.Step.Simplification.Data
                 ( SimplificationProof )
import           Kore.Unification.Error
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unifier

import Test.Tasty.HUnit.Extensions

instance EqualWithExplanation () where
    compareWithExplanation () () = Nothing
    printWithExplanation = show

instance EqualWithExplanation Natural where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

{-# ANN module ("HLint: ignore Use record patterns" :: String) #-}

instance
    ( EqualWithExplanation child
    , Eq child
    , Eq level
    , Show child
    , Eq1 domain
    , Show1 domain
    , EqualWithExplanation (variable level)
    , Eq (variable level)
    , Show (variable level)
    )
    => SumEqualWithExplanation (Pattern level domain variable child)
  where
    sumConstructorPair (AndPattern a1) (AndPattern a2) =
        SumConstructorSameWithArguments (EqWrap "AndPattern" a1 a2)
    sumConstructorPair pattern1@(AndPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (ApplicationPattern a1) (ApplicationPattern a2) =
        SumConstructorSameWithArguments (EqWrap "ApplicationPattern" a1 a2)
    sumConstructorPair pattern1@(ApplicationPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (BottomPattern a1) (BottomPattern a2) =
        SumConstructorSameWithArguments (EqWrap "BottomPattern" a1 a2)
    sumConstructorPair pattern1@(BottomPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (CeilPattern a1) (CeilPattern a2) =
        SumConstructorSameWithArguments (EqWrap "CeilPattern" a1 a2)
    sumConstructorPair pattern1@(CeilPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (DomainValuePattern a1) (DomainValuePattern a2) =
        SumConstructorSameWithArguments (EqWrap "DomainValuePattern" a1 a2)
    sumConstructorPair pattern1@(DomainValuePattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (EqualsPattern a1) (EqualsPattern a2) =
        SumConstructorSameWithArguments (EqWrap "EqualsPattern" a1 a2)
    sumConstructorPair pattern1@(EqualsPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (ExistsPattern a1) (ExistsPattern a2) =
        SumConstructorSameWithArguments (EqWrap "ExistsPattern" a1 a2)
    sumConstructorPair pattern1@(ExistsPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (FloorPattern a1) (FloorPattern a2) =
        SumConstructorSameWithArguments (EqWrap "FloorPattern" a1 a2)
    sumConstructorPair pattern1@(FloorPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (ForallPattern a1) (ForallPattern a2) =
        SumConstructorSameWithArguments (EqWrap "ForallPattern" a1 a2)
    sumConstructorPair pattern1@(ForallPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (IffPattern a1) (IffPattern a2) =
        SumConstructorSameWithArguments (EqWrap "IffPattern" a1 a2)
    sumConstructorPair pattern1@(IffPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (ImpliesPattern a1) (ImpliesPattern a2) =
        SumConstructorSameWithArguments (EqWrap "ImpliesPattern" a1 a2)
    sumConstructorPair pattern1@(ImpliesPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (InPattern a1) (InPattern a2) =
        SumConstructorSameWithArguments (EqWrap "InPattern" a1 a2)
    sumConstructorPair pattern1@(InPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (NextPattern a1) (NextPattern a2) =
        SumConstructorSameWithArguments (EqWrap "NextPattern" a1 a2)
    sumConstructorPair pattern1@(NextPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (NotPattern a1) (NotPattern a2) =
        SumConstructorSameWithArguments (EqWrap "NotPattern" a1 a2)
    sumConstructorPair pattern1@(NotPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (OrPattern a1) (OrPattern a2) =
        SumConstructorSameWithArguments (EqWrap "OrPattern" a1 a2)
    sumConstructorPair pattern1@(OrPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (RewritesPattern a1) (RewritesPattern a2) =
        SumConstructorSameWithArguments (EqWrap "RewritesPattern" a1 a2)
    sumConstructorPair pattern1@(RewritesPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (StringLiteralPattern a1) (StringLiteralPattern a2) =
        SumConstructorSameWithArguments (EqWrap "StringLiteralPattern" a1 a2)
    sumConstructorPair pattern1@(StringLiteralPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (CharLiteralPattern a1) (CharLiteralPattern a2) =
        SumConstructorSameWithArguments (EqWrap "CharLiteralPattern" a1 a2)
    sumConstructorPair pattern1@(CharLiteralPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TopPattern a1) (TopPattern a2) =
        SumConstructorSameWithArguments (EqWrap "TopPattern" a1 a2)
    sumConstructorPair pattern1@(TopPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (VariablePattern a1) (VariablePattern a2) =
        SumConstructorSameWithArguments (EqWrap "VariablePattern" a1 a2)
    sumConstructorPair pattern1@(VariablePattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

instance
    ( EqualWithExplanation child
    , Eq child, Eq level, Eq (variable level)
    , Show child
    , EqualWithExplanation (variable level)
    , Show (variable level)
    , Show1 domain
    , Eq1 domain
    ) => EqualWithExplanation (Pattern level domain variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (PurePattern level domain variable annotation)
    , Show1 domain
    , Eq1 domain
    , Show (variable level)
    , Eq (variable level)
    , EqualWithExplanation (variable level)
    , Show annotation
    , Eq annotation
    , Eq level
    , EqualWithExplanation annotation
    ) =>
    EqualWithExplanation (PurePattern level domain variable annotation)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (PurePattern level domain variable annotation)
    , Show1 domain
    , Eq1 domain
    , Show (variable level)
    , Eq (variable level)
    , EqualWithExplanation (variable level)
    , Show annotation
    , Eq annotation
    , Eq level
    , EqualWithExplanation annotation
    ) =>
    WrapperEqualWithExplanation (PurePattern level domain variable annotation)
  where
    wrapperField expected actual =
        EqWrap
            "getPurePattern = "
            (getPurePattern expected)
            (getPurePattern actual)
    wrapperConstructorName _ = "PurePattern"

instance
    ( Show (KorePattern domain variable annotation)
    , Show1 domain
    , Eq1 domain
    , Show annotation
    , Eq annotation
    , EqualWithExplanation annotation
    , EqualWithExplanation (variable Meta)
    , EqualWithExplanation (variable Object)
    , OrdMetaOrObject variable
    , ShowMetaOrObject variable
    ) =>
    EqualWithExplanation (KorePattern domain variable annotation)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (KorePattern domain variable annotation)
    , Eq1 domain, Show1 domain
    , Eq annotation, Show annotation
    , EqualWithExplanation annotation
    , EqualWithExplanation (variable Meta)
    , EqualWithExplanation (variable Object)
    , OrdMetaOrObject variable, ShowMetaOrObject variable
    ) =>
    WrapperEqualWithExplanation (KorePattern domain variable annotation)
  where
    wrapperField expected actual =
        EqWrap
            "getKorePattern = "
            (getKorePattern expected)
            (getKorePattern actual)
    wrapperConstructorName _ = "KorePattern"

instance
    ( Show (CofreeT f w a)
    , EqualWithExplanation (w (CofreeF f a (CofreeT f w a)))
    ) =>
    EqualWithExplanation (CofreeT f w a)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (CofreeT f w a)
    , EqualWithExplanation (w (CofreeF f a (CofreeT f w a)))
    ) =>
    WrapperEqualWithExplanation (CofreeT f w a)
  where
    wrapperField expected actual =
        EqWrap "runCofreeT = " (runCofreeT expected) (runCofreeT actual)
    wrapperConstructorName _ = "CofreeT"

instance
    ( EqualWithExplanation a, Show a ) =>
    EqualWithExplanation (Identity a)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation a, Show a ) =>
    WrapperEqualWithExplanation (Identity a)
  where
    wrapperField expected actual =
        EqWrap "runIdentity = " (runIdentity expected) (runIdentity actual)
    wrapperConstructorName _ = "Identity"

instance
    ( Show a, EqualWithExplanation a
    , Show (f b), EqualWithExplanation (f b)
    ) =>
    EqualWithExplanation (CofreeF f a b)
  where
    compareWithExplanation (a1 :< fb1) (a2 :< fb2) =
        compareWithExplanation a1 a2 <|> compareWithExplanation fb1 fb2
    printWithExplanation = show

instance
    ( Eq level, Show level
    , Eq (variable level), Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => SumEqualWithExplanation (StepProof level variable)
  where
    sumConstructorPair (StepProof a1) (StepProof a2) =
        SumConstructorSameWithArguments (EqWrap "StepProofCombined" a1 a2)

instance
    ( Eq level, Show level
    , Eq (variable level), Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => SumEqualWithExplanation (StepProofAtom level variable)
  where
    sumConstructorPair (StepProofUnification a1) (StepProofUnification a2) =
        SumConstructorSameWithArguments (EqWrap "StepProofUnification" a1 a2)
    sumConstructorPair a1@(StepProofUnification _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (StepProofVariableRenamings a1) (StepProofVariableRenamings a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "StepProofVariableRenamings" a1 a2)
    sumConstructorPair a1@(StepProofVariableRenamings _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (StepProofSimplification a1)
        (StepProofSimplification a2)
      =
        SumConstructorSameWithArguments (EqWrap "StepProofSimplification" a1 a2)
    sumConstructorPair a1@(StepProofSimplification _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    ( Eq level, Show level
    , Eq (variable level), Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (StepProofAtom level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq level, Show level
    , Eq (variable level), Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (StepProof level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (And level child)
  where
    structFieldsWithNames
        expected@(And _ _ _)
        actual@(And _ _ _)
      = [ EqWrap
            "andSort = "
            (andSort expected)
            (andSort actual)
        , EqWrap
            "andFirst = "
            (andFirst expected)
            (andFirst actual)
        , EqWrap
            "andSecond = "
            (andSecond expected)
            (andSecond actual)
        ]
    structConstructorName _ = "And"

instance (Show child, EqualWithExplanation child)
    => EqualWithExplanation (And level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Application level child)
  where
    structFieldsWithNames
        expected@(Application _ _)
        actual@(Application _ _)
      = [ EqWrap
            "applicationSymbolOrAlias = "
            (applicationSymbolOrAlias expected)
            (applicationSymbolOrAlias actual)
        , EqWrap
            "applicationChildren = "
            (applicationChildren expected)
            (applicationChildren actual)
        ]
    structConstructorName _ = "Application"

instance (Show child, EqualWithExplanation child)
    => EqualWithExplanation (Application level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Bottom level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Ceil level child)
  where
    structFieldsWithNames
        expected@(Ceil _ _ _)
        actual@(Ceil _ _ _)
      = [ EqWrap
            "ceilOperandSort = "
            (ceilOperandSort expected)
            (ceilOperandSort actual)
        , EqWrap
            "ceilResultSort = "
            (ceilResultSort expected)
            (ceilResultSort actual)
        , EqWrap
            "ceilChild = "
            (ceilChild expected)
            (ceilChild actual)
        ]
    structConstructorName _ = "Ceil"
instance (EqualWithExplanation child, Show child)
    => EqualWithExplanation (Ceil level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (Eq child, Show child, Eq1 domain, Show1 domain) =>
    EqualWithExplanation (DomainValue level domain child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Equals level child)
  where
    structFieldsWithNames
        expected@(Equals _ _ _ _)
        actual@(Equals _ _ _ _)
      = [ EqWrap
            "equalsResultSort = "
            (equalsResultSort expected)
            (equalsResultSort actual)
        , EqWrap
            "equalsOperandSort = "
            (equalsOperandSort expected)
            (equalsOperandSort actual)
        , EqWrap
            "equalsFirst = "
            (equalsFirst expected)
            (equalsFirst actual)
        , EqWrap
            "equalsSecond = "
            (equalsSecond expected)
            (equalsSecond actual)
        ]
    structConstructorName _ = "Equals"

instance (Show child, EqualWithExplanation child)
    => EqualWithExplanation (Equals level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Eq (variable level)
    , Show child
    , Show (variable level)
    , EqualWithExplanation child
    , EqualWithExplanation (variable level)
    )
    => StructEqualWithExplanation (Exists level variable child)
  where
    structFieldsWithNames
        expected@(Exists _ _ _)
        actual@(Exists _ _ _)
      = [ EqWrap
            "existsSort = "
            (existsSort expected)
            (existsSort actual)
        , EqWrap
            "existsVariable = "
            (existsVariable expected)
            (existsVariable actual)
        , EqWrap
            "existsChild = "
            (existsChild expected)
            (existsChild actual)
        ]
    structConstructorName _ = "Exists"
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation (variable level)
    , Eq (variable level)
    , Show (variable level)
    ) => EqualWithExplanation (Exists level variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Floor level child)
  where
    structFieldsWithNames
        expected@(Floor _ _ _)
        actual@(Floor _ _ _)
      = [ EqWrap
            "floorOperandSort = "
            (floorOperandSort expected)
            (floorOperandSort actual)
        , EqWrap
            "floorResultSort = "
            (floorResultSort expected)
            (floorResultSort actual)
        , EqWrap
            "floorChild = "
            (floorChild expected)
            (floorChild actual)
        ]
    structConstructorName _ = "Floor"
instance (Show child, EqualWithExplanation child)
    => EqualWithExplanation (Floor level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Eq (variable level)
    , Show child
    , Show (variable level)
    , EqualWithExplanation child
    , EqualWithExplanation (variable level)
    )
    => StructEqualWithExplanation (Forall level variable child)
  where
    structFieldsWithNames
        expected@(Forall _ _ _)
        actual@(Forall _ _ _)
      = [ EqWrap
            "forallSort = "
            (forallSort expected)
            (forallSort actual)
        , EqWrap
            "forallVariable = "
            (forallVariable expected)
            (forallVariable actual)
        , EqWrap
            "forallChild = "
            (forallChild expected)
            (forallChild actual)
        ]
    structConstructorName _ = "Forall"
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation (variable level)
    , Eq (variable level)
    , Show (variable level)
    ) => EqualWithExplanation (Forall level variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Show child
    , EqualWithExplanation child
    )
    => StructEqualWithExplanation (Iff level child)
  where
    structFieldsWithNames
        expected@(Iff _ _ _)
        actual@(Iff _ _ _)
      = [ EqWrap
            "iffSort = "
            (iffSort expected)
            (iffSort actual)
        , EqWrap
            "iffFirst = "
            (iffFirst expected)
            (iffFirst actual)
        , EqWrap
            "iffSecond = "
            (iffSecond expected)
            (iffSecond actual)
        ]
    structConstructorName _ = "Iff"
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    ) => EqualWithExplanation (Iff level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Implies level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (In level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Next level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, Eq child, EqualWithExplanation child)
  =>
    StructEqualWithExplanation (Not level child)
  where
    structFieldsWithNames
        expected@(Not _ _)
        actual@(Not _ _)
      = [ EqWrap
            "notSort = "
            (notSort expected)
            (notSort actual)
        , EqWrap
            "notChild = "
            (notChild expected)
            (notChild actual)
        ]
    structConstructorName _ = "Not"
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Not level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, Eq child, EqualWithExplanation child)
  =>
    StructEqualWithExplanation (Or level child)
  where
    structFieldsWithNames
        expected@(Or _ _ _)
        actual@(Or _ _ _)
      = [ EqWrap
            "orSort = "
            (orSort expected)
            (orSort actual)
        , EqWrap
            "orFirst = "
            (orFirst expected)
            (orFirst actual)
        , EqWrap
            "orSecond = "
            (orSecond expected)
            (orSecond actual)
        ]
    structConstructorName _ = "Or"
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Or level child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Rewrites level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance EqualWithExplanation StringLiteral
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance EqualWithExplanation CharLiteral
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Top level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (Variable level)
  where
    structFieldsWithNames
        expected@(Variable _ _)
        actual@(Variable _ _)
      = [ EqWrap
            "variableName = "
            (variableName expected)
            (variableName actual)
        , EqWrap
            "variableSort = "
            (variableSort expected)
            (variableSort actual)
        ]
    structConstructorName _ = "Variable"
instance EqualWithExplanation (Variable level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show


instance StructEqualWithExplanation (Id level)
    where
      structFieldsWithNames
          expected@(Id _ _)
          actual@(Id _ _)
        = [ EqWrap
              "getId = "
              (EWEString $ getIdForError expected)
              (EWEString $ getIdForError actual)
          , EqWrap
              "idLocation = "
              (EWEString "")
              (EWEString "")
          ]
      structConstructorName _ = "Id"
instance EqualWithExplanation (Id level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (Sort level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (SymbolOrAlias level)
    where
      structFieldsWithNames
          expected@(SymbolOrAlias _ _)
          actual@(SymbolOrAlias _ _)
        = [ EqWrap
              "symbolOrAliasConstructor = "
              (symbolOrAliasConstructor expected)
              (symbolOrAliasConstructor actual)
          , EqWrap
              "symbolOrAliasParams = "
              (symbolOrAliasParams expected)
              (symbolOrAliasParams actual)
          ]
      structConstructorName _ = "SymbolOrAlias"
instance EqualWithExplanation (SymbolOrAlias level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation UnificationError
  where
    sumConstructorPair UnsupportedPatterns UnsupportedPatterns =
        SumConstructorSameNoArguments

instance EqualWithExplanation UnificationError
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (ClashReason level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show (variable level), EqualWithExplanation (variable level))
    => SumEqualWithExplanation (SubstitutionError level variable)
  where
    sumConstructorPair
        (NonCtorCircularVariableDependency a1)
        (NonCtorCircularVariableDependency a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "NonCtorCircularVariableDependency" a1 a2)


instance (Show (variable level), EqualWithExplanation (variable level))
    => EqualWithExplanation (SubstitutionError level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance (Show (variable level), EqualWithExplanation (variable level))
    => SumEqualWithExplanation (StepError level variable)
  where
    sumConstructorPair (StepErrorUnification a1) (StepErrorUnification a2) =
        SumConstructorSameWithArguments (EqWrap "StepErrorUnification" a1 a2)
    sumConstructorPair a1@(StepErrorUnification _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (StepErrorSubstitution a1) (StepErrorSubstitution a2) =
        SumConstructorSameWithArguments (EqWrap "StepErrorSubstitution" a1 a2)
    sumConstructorPair a1@(StepErrorSubstitution _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance (Show (variable level), EqualWithExplanation (variable level))
    => EqualWithExplanation (StepError level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq (variable level)
    , Show (variable level)
    )
    => EqualWithExplanation (FunctionalProof level variable)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq (variable level)
    , Show (variable level)
    )
    => EqualWithExplanation (FunctionProof level variable)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq level, Eq (variable level)
    , Show level, Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => SumEqualWithExplanation (UnificationProof level variable)
  where
    sumConstructorPair EmptyUnificationProof EmptyUnificationProof =
        SumConstructorSameNoArguments
    sumConstructorPair a1@EmptyUnificationProof a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (CombinedUnificationProof a1) (CombinedUnificationProof a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "CombinedUnificationProof" a1 a2)
    sumConstructorPair a1@(CombinedUnificationProof _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (ConjunctionIdempotency a1) (ConjunctionIdempotency a2) =
        SumConstructorSameWithArguments (EqWrap "ConjunctionIdempotency" a1 a2)
    sumConstructorPair a1@(ConjunctionIdempotency _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (Proposition_5_24_3 a1 a2 a3) (Proposition_5_24_3 b1 b2 b3)
      =
        SumConstructorSameWithArguments
            (EqWrap "Proposition_5_24_3" (a1, a2, a3) (b1, b2, b3))
    sumConstructorPair a1@(Proposition_5_24_3 _ _ _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (AndDistributionAndConstraintLifting a1 a2)
        (AndDistributionAndConstraintLifting b1 b2) =
            SumConstructorSameWithArguments
                (EqWrap "AndDistributionAndConstraintLifting" (a1, a2) (b1, b2))
    sumConstructorPair a1@(AndDistributionAndConstraintLifting _ _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (SubstitutionMerge a1 a2 a3) (SubstitutionMerge b1 b2 b3)
      =
        SumConstructorSameWithArguments
            (EqWrap "SubstitutionMerge" (a1, a2, a3) (b1, b2, b3))
    sumConstructorPair a1@(SubstitutionMerge _ _ _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    ( Eq level, Eq (variable level)
    , Show level, Show (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (UnificationProof level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => StructEqualWithExplanation (VariableRenaming level variable)
  where
    structFieldsWithNames
        expected@(VariableRenaming _ _)
        actual@(VariableRenaming _ _)
      = [ EqWrap
            "variableRenamingOriginal = "
            (variableRenamingOriginal expected)
            (variableRenamingOriginal actual)
        , EqWrap
            "variableRenamingRenamed = "
            (variableRenamingRenamed expected)
            (variableRenamingRenamed actual)
        ]
    structConstructorName _ = "VariableRenaming"

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => EqualWithExplanation (VariableRenaming level variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => SumEqualWithExplanation (StepperVariable variable level)
  where
    sumConstructorPair (AxiomVariable a1) (AxiomVariable a2) =
        SumConstructorSameWithArguments (EqWrap "AxiomVariable" a1 a2)
    sumConstructorPair a1@(AxiomVariable _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (ConfigurationVariable a1) (ConfigurationVariable a2) =
        SumConstructorSameWithArguments (EqWrap "ConfigurationVariable" a1 a2)
    sumConstructorPair a1@(ConfigurationVariable _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => EqualWithExplanation (StepperVariable variable level)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    )
    => EqualWithExplanation (Substitution level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation (variable level)
    , Show level, Show (variable level)
    , Eq level, Eq (variable level)
    )
    => SumEqualWithExplanation (Substitution level variable)
  where
    sumConstructorPair s1 s2
        | s1Norm && s2Norm
            = SumConstructorSameWithArguments
                (EqWrap "NormalizedSubstitution" s1Inner s2Inner)
        | not s1Norm && not s2Norm
            = SumConstructorSameWithArguments
                (EqWrap "Substitution" s1Inner s2Inner)
        | otherwise =
            SumConstructorDifferent
                (printWithExplanation s1)
                (printWithExplanation s2)
      where
        s1Norm = Substitution.isNormalized s1
        s2Norm = Substitution.isNormalized s2
        s1Inner = Substitution.unwrap s1
        s2Inner = Substitution.unwrap s2

instance
    ( Show level, Show (variable level), Show child
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation child
    , EqualWithExplanation (StepPattern level variable)
    )
    => StructEqualWithExplanation (Predicated level variable child)
  where
    structFieldsWithNames expected actual =
        [ EqWrap
            "term = "
            (term expected)
            (term actual)
        , EqWrap
            "predicate = "
            (predicate expected)
            (predicate actual)
        , EqWrap
            "substitution = "
            (substitution expected)
            (substitution actual)
        ]
    structConstructorName _ = "Predicated"

instance
    ( Show level, Show (variable level), Show child
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation child
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (Predicated level variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation (variable level)
    , Eq level, Show level
    , Eq (variable level), Show (variable level)
    )
    => EqualWithExplanation (Predicate level variable)
  where
    compareWithExplanation p1 p2 = do
        compared <- traverse (\x -> traverse (compareWithExplanation x) p2) p1
        return $
            "Predicate ("
            ++ stringFromPredicate (compactPredicatePredicate compared)
            ++ ")"
    printWithExplanation = show


instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => SumEqualWithExplanation (AttemptedFunction level variable)
  where
    sumConstructorPair
        AttemptedFunction.NotApplicable
        AttemptedFunction.NotApplicable
      =
        SumConstructorSameNoArguments
    sumConstructorPair a1@AttemptedFunction.NotApplicable a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (AttemptedFunction.Applied a1) (AttemptedFunction.Applied a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "Applied" a1 a2)
    sumConstructorPair a1@(AttemptedFunction.Applied _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (AttemptedFunction level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (SimplificationProof level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    (Show a, EqualWithExplanation a)
    => SumEqualWithExplanation (MultiOr a)
  where
    sumConstructorPair (MultiOr a1) (MultiOr a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "MultiOr" a1 a2)

instance
    (Show a, EqualWithExplanation a)
    => EqualWithExplanation (MultiOr a)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (PatternAttributesError.FunctionError level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (PatternAttributesError.FunctionalError level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => SumEqualWithExplanation (UnificationOrSubstitutionError level variable)
  where
    sumConstructorPair (UnificationError a1) (UnificationError a2) =
        SumConstructorSameWithArguments (EqWrap "UnificationError" a1 a2)
    sumConstructorPair a1@(UnificationError _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (SubstitutionError a1) (SubstitutionError a2) =
        SumConstructorSameWithArguments (EqWrap "SubstitutionError" a1 a2)
    sumConstructorPair a1@(SubstitutionError _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    (EqualWithExplanation (variable level), Show (variable level))
    => EqualWithExplanation (UnificationOrSubstitutionError level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (variable Object), Show (variable Meta), Show child
    , Eq (variable Meta), Eq (variable Object), Eq child
    , EqualWithExplanation (variable Meta)
    , EqualWithExplanation (variable Object)
    , EqualWithExplanation child
    , Show1 domain
    , Eq1 domain
    )
    => EqualWithExplanation (UnifiedPattern domain variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (variable Object), Show (variable Meta), Show child
    , Eq (variable Meta), Eq (variable Object), Eq child
    , EqualWithExplanation (variable Object)
    , EqualWithExplanation (variable Meta)
    , EqualWithExplanation child
    , Show1 domain
    , Eq1 domain
    )
    => SumEqualWithExplanation (UnifiedPattern domain variable child)
  where
    sumConstructorPair (UnifiedMetaPattern p1) (UnifiedMetaPattern p2) =
        SumConstructorSameWithArguments (EqWrap "UnifiedMetaPattern" p1 p2)
    sumConstructorPair (UnifiedObjectPattern p1) (UnifiedObjectPattern p2) =
        SumConstructorSameWithArguments (EqWrap "UnifiedObjectPattern" p1 p2)
    sumConstructorPair p1 p2 =
        SumConstructorDifferent
            (printWithExplanation p1)
            (printWithExplanation p2)

instance
    ( EqualWithExplanation (a Meta)
    , EqualWithExplanation (a Object)
    , ShowMetaOrObject a
    ) =>
    SumEqualWithExplanation (Unified a)
  where
    sumConstructorPair (UnifiedMeta a1) (UnifiedMeta a2) =
        SumConstructorSameWithArguments (EqWrap "UnifiedMeta" a1 a2)
    sumConstructorPair (UnifiedObject a1) (UnifiedObject a2) =
        SumConstructorSameWithArguments (EqWrap "UnifiedObject" a1 a2)
    sumConstructorPair u1 u2 =
        SumConstructorDifferent
            (printWithExplanation u1)
            (printWithExplanation u2)

instance
    ( EqualWithExplanation (a Meta)
    , EqualWithExplanation (a Object)
    , Show (a Meta)
    , Show (a Object)
    , SumEqualWithExplanation (Unified a)
    )
    => EqualWithExplanation (Unified a)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => StructEqualWithExplanation (StepResult level variable)
  where
    structFieldsWithNames
        expected@(StepResult _ _)
        actual@(StepResult _ _)
      = [ EqWrap
            "rewrittenPattern = "
            (StepResult.rewrittenPattern expected)
            (StepResult.rewrittenPattern actual)
        , EqWrap
            "remainder = "
            (StepResult.remainder expected)
            (StepResult.remainder actual)
        ]
    structConstructorName _ = "StepResult"

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation (variable level)
    , EqualWithExplanation (StepPattern level variable)
    )
    => EqualWithExplanation (StepResult level variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation patt
    , Show patt
    , Eq patt
    )
    => SumEqualWithExplanation (StrategyPattern patt)
  where
    sumConstructorPair
        (StrategyPattern.RewritePattern p1) (StrategyPattern.RewritePattern p2)
      =
        SumConstructorSameWithArguments (EqWrap "RewritePattern" p1 p2)
    sumConstructorPair (StrategyPattern.Stuck p1) (StrategyPattern.Stuck p2) =
        SumConstructorSameWithArguments (EqWrap "Stuck" p1 p2)
    sumConstructorPair StrategyPattern.Bottom StrategyPattern.Bottom =
        SumConstructorSameNoArguments
    sumConstructorPair p1 p2 =
        SumConstructorDifferent
            (printWithExplanation p1)
            (printWithExplanation p2)

instance
    ( Show patt
    , SumEqualWithExplanation (StrategyPattern patt)
    )
    => EqualWithExplanation (StrategyPattern patt)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (Annotation.Null level) where
    compareWithExplanation _ _ = Nothing
    printWithExplanation = show

instance
    ( EqualWithExplanation variable, Show variable
    ) => StructEqualWithExplanation (Valid variable level)
  where
    structFieldsWithNames expected actual =
        [ EqWrap
            "patternSort = "
            (patternSort expected)
            (patternSort actual)
        , EqWrap
            "freeVariables = "
            (Kore.AST.Kore.freeVariables expected)
            (Kore.AST.Kore.freeVariables actual)
        ]
    structConstructorName _ = "Valid"

instance
    ( EqualWithExplanation variable, Show variable
    ) => EqualWithExplanation (Valid variable level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (PatternAttributesError.ConstructorLikeError)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (ConstructorLikeProof)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
