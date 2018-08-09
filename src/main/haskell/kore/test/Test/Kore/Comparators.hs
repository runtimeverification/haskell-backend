{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Test.Kore.Comparators
Description : Declares various data types involved in testing as instances of
              the 'EqualWithExplanation' class.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Test.Kore.Comparators where

import Data.Functor.Foldable
       ( Fix )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.Predicate.Predicate
import Kore.Step.BaseStep
import Kore.Step.Error
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..) )
import Kore.Step.Function.Data as AttemptedFunction
       ( AttemptedFunction (..) )
import Kore.Unification.Error
import Kore.Unification.Unifier

import Test.Tasty.HUnit.Extensions

{-# ANN module ("HLint: ignore Use record patterns" :: String) #-}

instance
    ( EqualWithExplanation child
    , Eq child, Eq level, Eq (variable level)
    , Show child
    , EqualWithExplanation (variable level)
    , Show (variable level))
    => SumEqualWithExplanation (Pattern level variable child)
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
    ) => EqualWithExplanation (Pattern level variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (Eq level, Show level) =>
    SumEqualWithExplanation (StepProof level)
  where
    sumConstructorPair (StepProofUnification a1) (StepProofUnification a2) =
        SumConstructorSameWithArguments (EqWrap "StepProofUnification" a1 a2)
    sumConstructorPair a1@(StepProofUnification _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (StepProofCombined a1) (StepProofCombined a2) =
        SumConstructorSameWithArguments (EqWrap "StepProofCombined" a1 a2)
    sumConstructorPair a1@(StepProofCombined _) a2 =
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

instance (Eq level, Show level) => EqualWithExplanation (StepProof level) where
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

instance EqualWithExplanation (DomainValue level (Fix (Pattern Meta Variable)))
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
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation (variable level)
    , Eq (variable level)
    , Show (variable level)
    ) => EqualWithExplanation (Exists level variable child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    ( EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Floor level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation (variable level)
    , Eq (variable level)
    , Show (variable level)
    ) => EqualWithExplanation (Forall level variable child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Iff level child)
  where
    compareWithExplanation = rawCompareWithExplanation
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
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Not level child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Or level child)
  where
    compareWithExplanation = rawCompareWithExplanation
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
              (EWEString $ getId expected)
              (EWEString $ getId actual)
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

instance SumEqualWithExplanation (UnificationError level)
  where
    sumConstructorPair (ConstructorClash a1 a2) (ConstructorClash b1 b2) =
        SumConstructorSameWithArguments
            (EqWrap "ConstructorClash" (a1, a2) (b1, b2))
    sumConstructorPair a1@(ConstructorClash _ _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (SortClash a1 a2) (SortClash b1 b2) =
        SumConstructorSameWithArguments (EqWrap "SortClash" (a1, a2) (b1,b2))
    sumConstructorPair a1@(SortClash _ _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (NonConstructorHead a1) (NonConstructorHead a2) =
        SumConstructorSameWithArguments
            (EqWrap "NonConstructorHead" a1 a2)
    sumConstructorPair a1@(NonConstructorHead _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (NonFunctionalHead a1) (NonFunctionalHead a2) =
        SumConstructorSameWithArguments
            (EqWrap "NonFunctionalHead" a1 a2)
    sumConstructorPair a1@(NonFunctionalHead _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair NonFunctionalPattern NonFunctionalPattern =
        SumConstructorSameNoArguments
    sumConstructorPair a1@NonFunctionalPattern a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair UnsupportedPatterns UnsupportedPatterns =
        SumConstructorSameNoArguments
    sumConstructorPair a1@UnsupportedPatterns a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair EmptyPatternList EmptyPatternList =
        SumConstructorSameNoArguments
    sumConstructorPair a1@EmptyPatternList a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance EqualWithExplanation (UnificationError level)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance (Show (variable level), EqualWithExplanation (variable level))
    => SumEqualWithExplanation (SubstitutionError level variable)
  where
    sumConstructorPair
        (CtorCircularVariableDependency a1) (CtorCircularVariableDependency a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "CtorCircularVariableDependency" a1 a2)
    sumConstructorPair
        a1@(CtorCircularVariableDependency _) a2
      =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)
    sumConstructorPair
        (NonCtorCircularVariableDependency a1)
        (NonCtorCircularVariableDependency a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "NonCtorCircularVariableDependency" a1 a2)
    sumConstructorPair
        a1@(NonCtorCircularVariableDependency _) a2
      =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)


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
    ( Eq level, Eq (variable level)
    , Show level, Show (variable level)
    , EqualWithExplanation (variable level)
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
    )
    => EqualWithExplanation (UnificationProof level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq level, Eq (variable level)
    , Show level, Show (variable level)
    , EqualWithExplanation (variable level)
    )
    => StructEqualWithExplanation (UnificationSolution level variable)
  where
    structFieldsWithNames
        expected@(UnificationSolution _ _)
        actual@(UnificationSolution _ _)
      = [ EqWrap
            "unificationSolutionTerm = "
            (unificationSolutionTerm expected)
            (unificationSolutionTerm actual)
        , EqWrap
            "unificationSolutionConstraints = "
            (unificationSolutionConstraints expected)
            (unificationSolutionConstraints actual)
        ]
    structConstructorName _ = "UnificationSolution"

instance
    ( Eq level, Eq (variable level)
    , Show level, Show (variable level)
    , EqualWithExplanation (variable level)
    )
    => EqualWithExplanation (UnificationSolution level variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (VariableRenaming level)
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

instance EqualWithExplanation (VariableRenaming level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation (StepperVariable level) where
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

instance EqualWithExplanation (StepperVariable level)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation(variable level)
    )
    => StructEqualWithExplanation (ExpandedPattern level variable)
  where
    structFieldsWithNames
        expected@(ExpandedPattern _ _ _)
        actual@(ExpandedPattern _ _ _)
      = [ EqWrap
            "term = "
            (ExpandedPattern.term expected)
            (ExpandedPattern.term actual)
        , EqWrap
            "predicate = "
            (ExpandedPattern.predicate expected)
            (ExpandedPattern.predicate actual)
        , EqWrap
            "substitution = "
            (ExpandedPattern.substitution expected)
            (ExpandedPattern.substitution actual)
        ]
    structConstructorName _ = "ExpandedPattern"

instance
    ( Show level, Show (variable level)
    , Eq level, Eq (variable level)
    , EqualWithExplanation(variable level)
    )
    => EqualWithExplanation (ExpandedPattern level variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation (PureMLPattern level variable)
    , Show level, Show (variable level)
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
    , EqualWithExplanation(variable level)
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
    , EqualWithExplanation(variable level)
    )
    => EqualWithExplanation (AttemptedFunction level variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show


instance EqualWithExplanation (PredicateProof level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
