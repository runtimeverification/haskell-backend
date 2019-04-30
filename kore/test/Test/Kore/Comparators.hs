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

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Comonad.Trans.Cofree
                 ( Cofree, CofreeF (..), CofreeT (..) )
import qualified Data.Function as Function
import           Data.Functor.Classes
import           Data.Functor.Identity
                 ( Identity (..) )
import           Numeric.Natural
                 ( Natural )

import qualified Kore.AllPath as AllPath
import qualified Kore.Annotation.Null as Annotation
import           Kore.Annotation.Valid
import           Kore.AST.Pure
import           Kore.AST.Sentence
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Location as Attribute
import qualified Kore.Attribute.Source as Attribute
import           Kore.Domain.Builtin
import           Kore.Error
import           Kore.OnePath.Step
                 ( StrategyPattern )
import           Kore.OnePath.Step as StrategyPattern
                 ( StrategyPattern (..) )
import           Kore.Predicate.Predicate
import           Kore.Proof.Functional
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Pattern
                 ( Conditional (..) )
import qualified Kore.Step.PatternAttributesError as PatternAttributesError
import           Kore.Step.Proof
import           Kore.Step.Representation.MultiOr
import           Kore.Step.Rule
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof )
import qualified Kore.Step.SMT.AST as SMT
                 ( Declarations (Declarations), Encodable,
                 IndirectSymbolDeclaration (IndirectSymbolDeclaration),
                 KoreSortDeclaration (..), KoreSymbolDeclaration (..),
                 Sort (Sort), SortReference (SortReference), Symbol (Symbol),
                 SymbolReference (SymbolReference) )
import qualified Kore.Step.SMT.AST as SMT.Declarations
                 ( Declarations (..) )
import qualified Kore.Step.SMT.AST as SMT.Symbol
                 ( Symbol (..) )
import qualified Kore.Step.SMT.AST as SMT.Sort
                 ( Sort (..) )
import qualified Kore.Step.SMT.AST as SMT.SortReference
                 ( SortReference (..) )
import qualified Kore.Step.SMT.AST as SMT.SymbolReference
                 ( SymbolReference (..) )
import qualified Kore.Step.SMT.AST as SMT.IndirectSymbolDeclaration
                 ( IndirectSymbolDeclaration (..) )
import           Kore.Step.TermLike
import qualified Kore.Syntax.SetVariable as SetVariable
import           Kore.Unification.Error
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unifier
import           Kore.Variables.Target
import qualified SMT.AST as SMT
                 ( Constructor (Constructor),
                 ConstructorArgument (ConstructorArgument),
                 DataTypeDeclaration (DataTypeDeclaration),
                 FunctionDeclaration (FunctionDeclaration), SExpr,
                 SortDeclaration (SortDeclaration), showSExpr )
import qualified SMT.AST as SMT.SortDeclaration
                 ( SortDeclaration (..) )
import qualified SMT.AST as SMT.FunctionDeclaration
                 ( FunctionDeclaration (..) )
import qualified SMT.AST as SMT.DataTypeDeclaration
                 ( DataTypeDeclaration (..) )
import qualified SMT.AST as SMT.Constructor
                 ( Constructor (..) )
import qualified SMT.AST as SMT.ConstructorArgument
                 ( ConstructorArgument (..) )

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
    , Eq Object
    , Show child
    , Eq1 domain
    , Show1 domain
    , EqualWithExplanation variable
    , EqualWithExplanation (domain child)
    , Eq variable
    , Show variable
    )
    => SumEqualWithExplanation (Pattern Object domain variable child)
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

    sumConstructorPair (InhabitantPattern s1) (InhabitantPattern s2) =
        SumConstructorSameWithArguments (EqWrap "InhabitantPattern" s1 s2)
    sumConstructorPair pattern1@(InhabitantPattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1)
            (printWithExplanation pattern2)

    sumConstructorPair (SetVariablePattern a1) (SetVariablePattern a2) =
        SumConstructorSameWithArguments (EqWrap "SetVariablePattern" a1 a2)
    sumConstructorPair pattern1@(SetVariablePattern _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

instance
    ( EqualWithExplanation child
    , Eq child, Eq Object, Eq variable
    , Show child
    , EqualWithExplanation variable
    , EqualWithExplanation (domain child)
    , Show variable
    , Show1 domain
    , Eq1 domain
    ) => EqualWithExplanation (Pattern Object domain variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show (PurePattern Object domain variable annotation)
    , Show1 domain
    , Eq1 domain
    , Show variable
    , Eq variable
    , EqualWithExplanation variable
    , Show annotation
    , Eq annotation
    , Eq Object
    , EqualWithExplanation annotation
    , EqualWithExplanation (domain (Cofree (Pattern Object domain variable) annotation))
    ) =>
    EqualWithExplanation (PurePattern Object domain variable annotation)
  where
    compareWithExplanation a@(PurePattern _) = wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    ( Show (PurePattern Object domain variable annotation)
    , Show1 domain
    , Eq1 domain
    , Show variable
    , Eq variable
    , EqualWithExplanation variable
    , Show annotation
    , Eq annotation
    , Eq Object
    , EqualWithExplanation annotation
    , EqualWithExplanation (domain (Cofree (Pattern Object domain variable) annotation))
    ) =>
    WrapperEqualWithExplanation (PurePattern Object domain variable annotation)
  where
    wrapperField expected actual =
        EqWrap
            "getPurePattern = "
            (getPurePattern expected)
            (getPurePattern actual)
    wrapperConstructorName _ = "PurePattern"

instance
    ( Show (CofreeT f w a)
    , EqualWithExplanation (w (CofreeF f a (CofreeT f w a)))
    ) =>
    EqualWithExplanation (CofreeT f w a)
  where
    compareWithExplanation a@(CofreeT _) = wrapperCompareWithExplanation a
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
    compareWithExplanation a@(Identity _) = wrapperCompareWithExplanation a
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
        compareWithExplanation fb1 fb2 <|> compareWithExplanation a1 a2
    printWithExplanation = show

instance
    ( Eq Object, Show Object
    , Eq variable, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => SumEqualWithExplanation (StepProof Object variable)
  where
    sumConstructorPair (StepProof a1) (StepProof a2) =
        SumConstructorSameWithArguments (EqWrap "StepProofCombined" a1 a2)

instance
    ( Eq Object, Show Object
    , Eq variable, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => SumEqualWithExplanation (StepProofAtom Object variable)
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
    ( Eq Object, Show Object
    , Eq variable, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (StepProofAtom Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq Object, Show Object
    , Eq variable, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (StepProof Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (And Sort child)
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
    => EqualWithExplanation (And Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Application SymbolOrAlias child)
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
    => EqualWithExplanation (Application SymbolOrAlias child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Bottom Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Ceil Sort child)
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
    => EqualWithExplanation (Ceil Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (Eq child, Show child, Eq1 domain, Show1 domain) =>
    EqualWithExplanation (DomainValue Sort domain child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Equals Sort child)
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
    => EqualWithExplanation (Equals Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Eq variable
    , Show child
    , Show variable
    , EqualWithExplanation child
    , EqualWithExplanation variable
    )
    => StructEqualWithExplanation (Exists Object variable child)
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
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    ) => EqualWithExplanation (Exists Object variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, EqualWithExplanation child)
    => StructEqualWithExplanation (Floor Sort child)
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
    => EqualWithExplanation (Floor Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Eq variable
    , Show child
    , Show variable
    , EqualWithExplanation child
    , EqualWithExplanation variable
    )
    => StructEqualWithExplanation (Forall Object variable child)
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
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    ) => EqualWithExplanation (Forall Object variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Show child
    , EqualWithExplanation child
    )
    => StructEqualWithExplanation (Iff Object child)
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
    ) => EqualWithExplanation (Iff Object child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Implies Object child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (In Object child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Next Object child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, Eq child, EqualWithExplanation child)
  =>
    StructEqualWithExplanation (Not Object child)
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
    => EqualWithExplanation (Not Object child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (Show child, Eq child, EqualWithExplanation child)
  =>
    StructEqualWithExplanation (Or Sort child)
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
    => EqualWithExplanation (Or Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Rewrites Object child)
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
    => EqualWithExplanation (Top Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => WrapperEqualWithExplanation (SetVariable variable)
  where
    wrapperConstructorName _ = "SetVariable"
    wrapperField =
        Function.on (EqWrap "getVariable = ") SetVariable.getVariable

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (SetVariable variable)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Variable where
    structFieldsWithNames
        expected@(Variable _ _ _)
        actual@(Variable _ _ _)
      = [ EqWrap
            "variableName = "
            (variableName expected)
            (variableName actual)
        , EqWrap
            "variableCounter = "
            (variableCounter expected)
            (variableCounter actual)
        , EqWrap
            "variableSort = "
            (variableSort expected)
            (variableSort actual)
        ]
    structConstructorName _ = "Variable"

instance EqualWithExplanation Variable where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation Concrete where
    compareWithExplanation = \case {}
    printWithExplanation = \case {}

instance StructEqualWithExplanation Id where
    structFieldsWithNames expected@(Id _ _) actual@(Id _ _) =
        map (\f -> f expected actual)
            [ Function.on (EqWrap "getId = ") getIdForError
            , Function.on (EqWrap "idLocation = ") (const ())
            ]
    structConstructorName _ = "Id"

instance EqualWithExplanation Id where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation Sort where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation SymbolOrAlias
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
instance EqualWithExplanation SymbolOrAlias
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation UnificationError
  where
    sumConstructorPair UnsupportedPatterns UnsupportedPatterns =
        SumConstructorSameNoArguments
    sumConstructorPair (UnsupportedSymbolic a) (UnsupportedSymbolic b) =
        SumConstructorSameWithArguments
        $ EqWrap "UnsupportedSymbolic" (show a) (show b)
    sumConstructorPair a b =
        Function.on SumConstructorDifferent printWithExplanation a b

instance EqualWithExplanation UnificationError
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (ClashReason Object)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show variable, EqualWithExplanation variable)
    => SumEqualWithExplanation (SubstitutionError Object variable)
  where
    sumConstructorPair
        (NonCtorCircularVariableDependency a1)
        (NonCtorCircularVariableDependency a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "NonCtorCircularVariableDependency" a1 a2)


instance (Show variable, EqualWithExplanation variable)
    => EqualWithExplanation (SubstitutionError Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq variable
    , Show variable
    )
    => EqualWithExplanation (FunctionalProof Object variable)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq variable
    , Show variable
    )
    => EqualWithExplanation (FunctionProof Object variable)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq Object, Eq variable
    , Show Object, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => SumEqualWithExplanation (UnificationProof Object variable)
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
    ( Eq Object, Eq variable
    , Show Object, Show variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (UnificationProof Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation variable, Show variable)
    => StructEqualWithExplanation (VariableRenaming Object variable)
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
    (EqualWithExplanation variable, Show variable)
    => EqualWithExplanation (VariableRenaming Object variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation variable, Show variable)
    => SumEqualWithExplanation (Target variable)
  where
    sumConstructorPair (Target a1) (Target a2) =
        SumConstructorSameWithArguments (EqWrap "Target" a1 a2)
    sumConstructorPair a1@(Target _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair (NonTarget a1) (NonTarget a2) =
        SumConstructorSameWithArguments (EqWrap "NonTarget" a1 a2)
    sumConstructorPair a1@(NonTarget _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    (EqualWithExplanation variable, Show variable)
    => EqualWithExplanation (Target variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show Object, Show variable
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    )
    => EqualWithExplanation (Substitution variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    EqualWithExplanation (Builtin child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (External child) where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (External child) where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "domainValueSort = ")
            Kore.Domain.Builtin.domainValueSort
            expect
            actual
        , Function.on (EqWrap "domainValueChild = ")
            Kore.Domain.Builtin.domainValueChild
            expect
            actual
        ]
    structConstructorName _ = "External"

instance EqualWithExplanation InternalInt where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation InternalInt where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "builtinIntSort = ") builtinIntSort expect actual
        , Function.on (EqWrap "builtinIntValue = ") builtinIntValue expect actual
        ]
    structConstructorName _ = "InternalInt"

instance EqualWithExplanation InternalBool where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation InternalBool where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "builtinBoolSort = ") builtinBoolSort expect actual
        , Function.on (EqWrap "builtinBoolValue = ") builtinBoolValue expect actual
        ]
    structConstructorName _ = "InternalBool"

instance
    (EqualWithExplanation child, Show child) =>
    EqualWithExplanation (InternalMap child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    StructEqualWithExplanation (InternalMap child)
  where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "builtinMapSort = ") builtinMapSort expect actual
        , Function.on (EqWrap "builtinMapUnit = ") builtinMapUnit expect actual
        , Function.on (EqWrap "builtinMapElement = ") builtinMapElement expect actual
        , Function.on (EqWrap "builtinMapConcat = ") builtinMapConcat expect actual
        , Function.on (EqWrap "builtinMapChild = ") builtinMapChild expect actual
        ]
    structConstructorName _ = "InternalMap"

instance
    (EqualWithExplanation child, Show child) =>
    EqualWithExplanation (InternalList child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    StructEqualWithExplanation (InternalList child)
  where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "builtinListSort = ") builtinListSort expect actual
        , Function.on (EqWrap "builtinListUnit = ") builtinListUnit expect actual
        , Function.on (EqWrap "builtinListElement = ") builtinListElement expect actual
        , Function.on (EqWrap "builtinListConcat = ") builtinListConcat expect actual
        , Function.on (EqWrap "builtinListChild = ") builtinListChild expect actual
        ]
    structConstructorName _ = "InternalList"

instance EqualWithExplanation InternalSet where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation InternalSet where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "builtinSetSort = ") builtinSetSort expect actual
        , Function.on (EqWrap "builtinSetUnit = ") builtinSetUnit expect actual
        , Function.on (EqWrap "builtinSetElement = ") builtinSetElement expect actual
        , Function.on (EqWrap "builtinSetConcat = ") builtinSetConcat expect actual
        , Function.on (EqWrap "builtinSetChild = ") builtinSetChild expect actual
        ]
    structConstructorName _ = "InternalSet"

instance
    (EqualWithExplanation child, Show child) =>
    SumEqualWithExplanation (Builtin child)
  where
    sumConstructorPair (BuiltinExternal ext1) (BuiltinExternal ext2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinExternal" ext1 ext2)
    sumConstructorPair (BuiltinInt int1) (BuiltinInt int2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinInt" int1 int2)
    sumConstructorPair (BuiltinBool bool1) (BuiltinBool bool2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinBool" bool1 bool2)
    sumConstructorPair (BuiltinMap map1) (BuiltinMap map2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinMap" map1 map2)
    sumConstructorPair (BuiltinList list1) (BuiltinList list2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinList" list1 list2)
    sumConstructorPair (BuiltinSet set1) (BuiltinSet set2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinSet" set1 set2)
    sumConstructorPair a b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

instance
    ( EqualWithExplanation variable
    , Show Object, Show variable
    , Eq Object, Eq variable
    )
    => SumEqualWithExplanation (Substitution variable)
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
    ( Show Object, Show variable, Show child
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    , EqualWithExplanation child
    , EqualWithExplanation (TermLike variable)
    )
    => StructEqualWithExplanation (Conditional Object variable child)
  where
    structFieldsWithNames
        expected@(Conditional _ _ _) actual@(Conditional _ _ _)
      =
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
    structConstructorName _ = "Conditional"

instance
    ( Show Object, Show variable, Show child
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    , EqualWithExplanation child
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (Conditional Object variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation variable
    , Eq Object, Show Object
    , Eq variable, Show variable
    )
    => EqualWithExplanation (Predicate variable)
  where
    compareWithExplanation p1 p2 = do
        compared <- traverse (\x -> traverse (compareWithExplanation x) p2) p1
        return $
            "Predicate ("
            ++ stringFromPredicate (compactPredicatePredicate compared)
            ++ ")"
    printWithExplanation = show

instance
    ( Show Object, Show variable
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    )
    => StructEqualWithExplanation (AttemptedAxiomResults Object variable)
  where
    structFieldsWithNames
        expected@(AttemptedAxiomResults _ _)
        actual@(AttemptedAxiomResults _ _)
      =
        [ EqWrap
            "results = "
            (AttemptedAxiomResults.results expected)
            (AttemptedAxiomResults.results actual)
        , EqWrap
            "remainders = "
            (AttemptedAxiomResults.remainders expected)
            (AttemptedAxiomResults.remainders actual)
        ]
    structConstructorName _ = "AttemptedAxiomResults"

instance
    ( Show Object, Show variable
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    )
    => EqualWithExplanation (AttemptedAxiomResults Object variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Show Object, Show variable
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => SumEqualWithExplanation (AttemptedAxiom Object variable)
  where
    sumConstructorPair
        AttemptedAxiom.NotApplicable
        AttemptedAxiom.NotApplicable
      =
        SumConstructorSameNoArguments
    sumConstructorPair a1@AttemptedAxiom.NotApplicable a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

    sumConstructorPair
        (AttemptedAxiom.Applied a1) (AttemptedAxiom.Applied a2)
      =
        SumConstructorSameWithArguments
            (EqWrap "Applied" a1 a2)
    sumConstructorPair a1@(AttemptedAxiom.Applied _) a2 =
        SumConstructorDifferent
            (printWithExplanation a1) (printWithExplanation a2)

instance
    ( Show Object, Show variable
    , Eq Object, Eq variable
    , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (AttemptedAxiom Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (SimplificationProof Object)
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

instance EqualWithExplanation (PatternAttributesError.FunctionError Object)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (PatternAttributesError.FunctionalError Object)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation variable, Show variable)
    => SumEqualWithExplanation (UnificationOrSubstitutionError Object variable)
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
    (EqualWithExplanation variable, Show variable)
    => EqualWithExplanation (UnificationOrSubstitutionError Object variable)
  where
    compareWithExplanation = sumCompareWithExplanation
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

instance EqualWithExplanation (Annotation.Null Object) where
    compareWithExplanation _ _ = Nothing
    printWithExplanation = show

instance
    ( EqualWithExplanation variable, Show variable
    ) => StructEqualWithExplanation (Valid variable level)
  where
    structFieldsWithNames expected@(Valid _ _) actual@(Valid _ _) =
        [ EqWrap
            "patternSort = "
            (patternSort expected)
            (patternSort actual)
        , EqWrap
            "freeVariables = "
            (Kore.Annotation.Valid.freeVariables expected)
            (Kore.Annotation.Valid.freeVariables actual)
        ]
    structConstructorName _ = "Valid"

instance
    ( EqualWithExplanation variable, Show variable
    ) => EqualWithExplanation (Valid variable level)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation PatternAttributesError.ConstructorLikeError
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation ConstructorLikeProof
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show


instance SumEqualWithExplanation (AxiomIdentifier Object)
  where
    sumConstructorPair
        (AxiomIdentifier.Application p1) (AxiomIdentifier.Application p2)
      =
        SumConstructorSameWithArguments (EqWrap "Application" p1 p2)
    sumConstructorPair
        (AxiomIdentifier.Ceil p1) (AxiomIdentifier.Ceil p2)
      =
        SumConstructorSameWithArguments (EqWrap "Ceil" p1 p2)
    sumConstructorPair p1 p2 =
        SumConstructorDifferent
            (printWithExplanation p1)
            (printWithExplanation p2)

instance EqualWithExplanation (AxiomIdentifier Object)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Ord  variable
    , Show variable
    , EqualWithExplanation variable
    ) =>
    EqualWithExplanation (RulePattern Object variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Ord  variable
    , Show variable
    , EqualWithExplanation variable
    ) =>
    StructEqualWithExplanation (RulePattern Object variable)
  where
    structConstructorName _ = "RulePattern"
    structFieldsWithNames
        expect@(RulePattern _ _ _ _ _)
        actual@(RulePattern _ _ _ _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "left = "      ) left
            , Function.on (EqWrap "right = "     ) right
            , Function.on (EqWrap "requires = "  ) requires
            , Function.on (EqWrap "ensures = "   ) ensures
            , Function.on (EqWrap "attributes = ") attributes
            ]

instance EqualWithExplanation Attribute.Axiom where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Attribute.Axiom where
    structConstructorName _ = "Axiom"
    structFieldsWithNames
        expect@(Attribute.Axiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        actual@(Attribute.Axiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "heatCool = "       ) Attribute.heatCool
            , Function.on (EqWrap "productionID = "   ) Attribute.productionID
            , Function.on (EqWrap "assoc = "          ) Attribute.assoc
            , Function.on (EqWrap "comm = "           ) Attribute.comm
            , Function.on (EqWrap "unit = "           ) Attribute.unit
            , Function.on (EqWrap "idem = "           ) Attribute.idem
            , Function.on (EqWrap "trusted = "        ) Attribute.trusted
            , Function.on (EqWrap "concrete = "       ) Attribute.concrete
            , Function.on (EqWrap "simplification = " ) Attribute.simplification
            , Function.on (EqWrap "overload = "       ) Attribute.overload
            , Function.on (EqWrap "smtLemma = "       ) Attribute.smtLemma
            , Function.on (EqWrap "label = "          ) Attribute.label
            , Function.on (EqWrap "sorceLocation = "  ) Attribute.sourceLocation
            , Function.on (EqWrap "constructor = "    ) Attribute.constructor
            , Function.on (EqWrap "identifier = "     ) Attribute.identifier
            ]

instance EqualWithExplanation Attribute.HeatCool where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation Attribute.HeatCool where
    sumConstructorPair Attribute.Heat   Attribute.Heat   =
        SumConstructorSameNoArguments
    sumConstructorPair Attribute.Normal Attribute.Normal =
        SumConstructorSameNoArguments
    sumConstructorPair Attribute.Cool   Attribute.Cool   =
        SumConstructorSameNoArguments
    sumConstructorPair expect           actual           =
        SumConstructorDifferent (show expect) (show actual)

instance EqualWithExplanation Attribute.ProductionID where
    compareWithExplanation a@(Attribute.ProductionID _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.ProductionID where
    wrapperConstructorName _ = "ProductionID"
    wrapperField =
        Function.on (EqWrap "getProductionID = ") Attribute.getProductionID

instance EqualWithExplanation Attribute.Assoc where
    compareWithExplanation a@(Attribute.Assoc _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Assoc where
    wrapperConstructorName _ = "Assoc"
    wrapperField = Function.on (EqWrap "isAssoc = ") Attribute.isAssoc

instance EqualWithExplanation Attribute.Comm where
    compareWithExplanation a@(Attribute.Comm _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Comm where
    wrapperConstructorName _ = "Comm"
    wrapperField = Function.on (EqWrap "isComm = ") Attribute.isComm

instance EqualWithExplanation Attribute.Unit where
    compareWithExplanation a@(Attribute.Unit _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Unit where
    wrapperConstructorName _ = "Unit"
    wrapperField = Function.on (EqWrap "isUnit = ") Attribute.isUnit

instance EqualWithExplanation Attribute.Idem where
    compareWithExplanation a@(Attribute.Idem _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Idem where
    wrapperConstructorName _ = "Idem"
    wrapperField = Function.on (EqWrap "isIdem = ") Attribute.isIdem

instance EqualWithExplanation Attribute.Trusted where
    compareWithExplanation a@(Attribute.Trusted _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Trusted where
    wrapperConstructorName _ = "Trusted"
    wrapperField = Function.on (EqWrap "isTrusted = ") Attribute.isTrusted

instance EqualWithExplanation Attribute.Concrete where
    compareWithExplanation a@(Attribute.Concrete _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Concrete where
    wrapperConstructorName _ = "Concrete"
    wrapperField = Function.on (EqWrap "isConcrete = ") Attribute.isConcrete

instance EqualWithExplanation Attribute.Simplification where
    compareWithExplanation a@(Attribute.Simplification _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Simplification where
    wrapperConstructorName _ = "Simplification"
    wrapperField =
        Function.on (EqWrap "isSimplification = ") Attribute.isSimplification

instance EqualWithExplanation Attribute.Overload where
    compareWithExplanation a@(Attribute.Overload _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Overload where
    wrapperConstructorName _ = "Overload"
    wrapperField = Function.on (EqWrap "getOverload = ") Attribute.getOverload

instance EqualWithExplanation Attribute.SmtLemma where
    compareWithExplanation a@(Attribute.SmtLemma _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.SmtLemma where
    wrapperConstructorName _ = "SmtLemma"
    wrapperField = Function.on (EqWrap "isSmtLemma = ") Attribute.isSmtLemma

instance EqualWithExplanation Attribute.Label where
    compareWithExplanation a@(Attribute.Label _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Label where
    wrapperConstructorName _ = "Label"
    wrapperField = Function.on (EqWrap "unLabel = ") Attribute.unLabel

instance
    EqualWithExplanation Attribute.RuleIndex
  where
    compareWithExplanation a@(Attribute.RuleIndex _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    WrapperEqualWithExplanation Attribute.RuleIndex
  where
    wrapperField = Function.on (EqWrap "getRuleIndex = ") Attribute.getRuleIndex
    wrapperConstructorName _ = "RuleIndex"

instance
    EqualWithExplanation Attribute.Constructor
  where
    compareWithExplanation a@(Attribute.Constructor _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    WrapperEqualWithExplanation Attribute.Constructor
  where
    wrapperField =
        Function.on (EqWrap "isConstructor = ") Attribute.isConstructor
    wrapperConstructorName _ = "Constructor"

instance EqualWithExplanation Attribute.SourceLocation
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Attribute.SourceLocation
  where
    structConstructorName _ = "SourceLocation"
    structFieldsWithNames
        expect@(Attribute.SourceLocation _ _)
        actual@(Attribute.SourceLocation _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "location = ") Attribute.location
            , Function.on (EqWrap "source = ") Attribute.source
            ]

instance EqualWithExplanation Attribute.Location
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Attribute.Location
  where
    structConstructorName _ = "Location"
    structFieldsWithNames
        expect@(Attribute.Location _ _)
        actual@(Attribute.Location _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "start = ") Attribute.start
            , Function.on (EqWrap "end = ") Attribute.end
            ]

instance EqualWithExplanation Attribute.LineColumn
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Attribute.LineColumn
  where
    structConstructorName _ = "LineColumn"
    structFieldsWithNames
        expect@(Attribute.LineColumn _ _)
        actual@(Attribute.LineColumn _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "start = ") Attribute.line
            , Function.on (EqWrap "end = ") Attribute.column
            ]

instance
    EqualWithExplanation Attribute.Source
  where
    compareWithExplanation a@(Attribute.Source _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    WrapperEqualWithExplanation Attribute.Source
  where
    wrapperField = Function.on (EqWrap "unSource = ") Attribute.unSource
    wrapperConstructorName _ = "Source"

-- For: Alias

instance EqualWithExplanation (Alias Object) where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (Alias Object) where
    structConstructorName _ = "Alias"
    structFieldsWithNames expect@(Alias _ _) actual@(Alias _ _) =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "aliasConstructor = ") aliasConstructor
            , Function.on (EqWrap "aliasParams = ") aliasParams
            ]

-- For: SortVariable

instance EqualWithExplanation SortVariable where
    compareWithExplanation a@(SortVariable _) = wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation SortVariable where
    wrapperField = Function.on (EqWrap "getSortVariable = ") getSortVariable
    wrapperConstructorName _ = "SortVariable"

-- For: Error

instance
    EqualWithExplanation (Error a)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    StructEqualWithExplanation (Error a)
  where
    structFieldsWithNames (Error expectedContext expectedMessage)
                          (Error actualContext   actualMessage) =
        [ EqWrap "errorMessage = " expectedMessage actualMessage
        , EqWrap "errorContext = " expectedContext actualContext
        ]
    structConstructorName _ = "Error"

-- For∷ Attributes

instance
    EqualWithExplanation Attributes
  where
    compareWithExplanation a@(Attributes _) = wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    WrapperEqualWithExplanation Attributes
  where
    wrapperField = Function.on (EqWrap "getAttributes = ") getAttributes
    wrapperConstructorName _ = "Attributes"

instance
    (EqualWithExplanation goal, Show goal)
    => EqualWithExplanation (AllPath.ProofState goal)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation goal, Show goal)
    => SumEqualWithExplanation (AllPath.ProofState goal)
  where
    sumConstructorPair AllPath.Proven          AllPath.Proven          =
        SumConstructorSameNoArguments
    sumConstructorPair (AllPath.Goal goal1)    (AllPath.Goal goal2)    =
        SumConstructorSameWithArguments (EqWrap "Goal" goal1 goal2)
    sumConstructorPair (AllPath.GoalRem goal1) (AllPath.GoalRem goal2) =
        SumConstructorSameWithArguments (EqWrap "GoalRem" goal1 goal2)
    sumConstructorPair expect           actual           =
        SumConstructorDifferent (show expect) (show actual)

-- SMT.AST

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.Declarations sort symbol name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.Declarations sort symbol name)
  where
    structFieldsWithNames
        expect@(SMT.Declarations _ _)
        actual@(SMT.Declarations _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "sorts = ") SMT.Declarations.sorts
            , Function.on (EqWrap "symbols = ") SMT.Declarations.symbols
            ]
    structConstructorName _ = "Declarations"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.Sort sort symbol name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.Sort sort symbol name)
  where
    structFieldsWithNames
        expect@(SMT.Sort _ _)
        actual@(SMT.Sort _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "declaration = ") SMT.Sort.declaration
            ]
    structConstructorName _ = "Sort"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.Symbol sort name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.Symbol sort name)
  where
    structFieldsWithNames
        expect@(SMT.Symbol _ _)
        actual@(SMT.Symbol _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "declaration = ") SMT.Symbol.declaration
            ]
    structConstructorName _ = "Symbol"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.KoreSymbolDeclaration sort name)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => SumEqualWithExplanation (SMT.KoreSymbolDeclaration sort name)
  where
    sumConstructorPair
        (SMT.SymbolDeclaredDirectly a) (SMT.SymbolDeclaredDirectly b)
      =
        SumConstructorSameWithArguments (EqWrap "SymbolDeclaredDirectly" a b)
    sumConstructorPair a@(SMT.SymbolDeclaredDirectly _) b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

    sumConstructorPair
        (SMT.SymbolDeclaredIndirectly a)
        (SMT.SymbolDeclaredIndirectly b)
      =
        SumConstructorSameWithArguments (EqWrap "SymbolDeclaredIndirectly" a b)
    sumConstructorPair a@(SMT.SymbolDeclaredIndirectly _) b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.IndirectSymbolDeclaration sort name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.IndirectSymbolDeclaration sort name)
  where
    structFieldsWithNames
        expect@(SMT.IndirectSymbolDeclaration _ _)
        actual@(SMT.IndirectSymbolDeclaration _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.IndirectSymbolDeclaration.name
            , Function.on (EqWrap "sorts = ")
                SMT.IndirectSymbolDeclaration.sorts
            ]
    structConstructorName _ = "IndirectSymbolDeclaration"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.FunctionDeclaration sort name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.FunctionDeclaration sort name)
  where
    structFieldsWithNames
        expect@(SMT.FunctionDeclaration _ _ _)
        actual@(SMT.FunctionDeclaration _ _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.FunctionDeclaration.name
            , Function.on (EqWrap "inputSorts = ")
                SMT.FunctionDeclaration.inputSorts
            , Function.on (EqWrap "resultSort = ")
                SMT.FunctionDeclaration.resultSort
            ]
    structConstructorName _ = "FunctionDeclaration"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.KoreSortDeclaration sort symbol name)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => SumEqualWithExplanation (SMT.KoreSortDeclaration sort symbol name)
  where
    sumConstructorPair
        (SMT.SortDeclarationDataType a) (SMT.SortDeclarationDataType b)
      =
        SumConstructorSameWithArguments (EqWrap "SortDeclarationDataType" a b)
    sumConstructorPair a@(SMT.SortDeclarationDataType _) b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

    sumConstructorPair
        (SMT.SortDeclarationSort a) (SMT.SortDeclarationSort b)
      =
        SumConstructorSameWithArguments (EqWrap "SortDeclarationSort" a b)
    sumConstructorPair a@(SMT.SortDeclarationSort _) b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

    sumConstructorPair
        (SMT.SortDeclaredIndirectly a)
        (SMT.SortDeclaredIndirectly b)
      =
        SumConstructorSameWithArguments (EqWrap "SortDeclaredIndirectly" a b)
    sumConstructorPair a@(SMT.SortDeclaredIndirectly _) b =
        SumConstructorDifferent
            (printWithExplanation a)
            (printWithExplanation b)

instance
    ( EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.SortDeclaration name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.SortDeclaration name)
  where
    structFieldsWithNames
        expect@(SMT.SortDeclaration _ _)
        actual@(SMT.SortDeclaration _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.SortDeclaration.name
            , Function.on (EqWrap "arity = ") SMT.SortDeclaration.arity
            ]
    structConstructorName _ = "SortDeclaration"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.DataTypeDeclaration sort symbol name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.DataTypeDeclaration sort symbol name)
  where
    structFieldsWithNames
        expect@(SMT.DataTypeDeclaration _ _ _)
        actual@(SMT.DataTypeDeclaration _ _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.DataTypeDeclaration.name
            , Function.on (EqWrap "typeArguments = ")
                SMT.DataTypeDeclaration.typeArguments
            , Function.on (EqWrap "constructors = ")
                SMT.DataTypeDeclaration.constructors
            ]
    structConstructorName _ = "DataTypeDeclaration"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.Constructor sort symbol name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation symbol, Show symbol
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.Constructor sort symbol name)
  where
    structFieldsWithNames
        expect@(SMT.Constructor _ _)
        actual@(SMT.Constructor _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.Constructor.name
            , Function.on (EqWrap "arguments = ") SMT.Constructor.arguments
            ]
    structConstructorName _ = "Constructor"

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => EqualWithExplanation (SMT.ConstructorArgument sort name)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation sort, Show sort
    , EqualWithExplanation name, Show name
    )
    => StructEqualWithExplanation (SMT.ConstructorArgument sort name)
  where
    structFieldsWithNames
        expect@(SMT.ConstructorArgument _ _)
        actual@(SMT.ConstructorArgument _ _)
      =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "name = ") SMT.ConstructorArgument.name
            , Function.on (EqWrap "argType = ") SMT.ConstructorArgument.argType
            ]
    structConstructorName _ = "ConstructorArgument"

instance EqualWithExplanation SMT.SExpr where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = SMT.showSExpr

instance EqualWithExplanation SMT.SortReference
  where
    compareWithExplanation a@(SMT.SortReference _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation SMT.SortReference
  where
    wrapperField =
        Function.on (EqWrap "getSortReference = ")
            SMT.SortReference.getSortReference
    wrapperConstructorName _ = "SortReference"

instance EqualWithExplanation SMT.SymbolReference
  where
    compareWithExplanation a@(SMT.SymbolReference _) =
        wrapperCompareWithExplanation a
    printWithExplanation = show

instance WrapperEqualWithExplanation SMT.SymbolReference
  where
    wrapperField =
        Function.on (EqWrap "getSymbolReference = ")
            SMT.SymbolReference.getSymbolReference
    wrapperConstructorName _ = "SymbolReference"

instance EqualWithExplanation SMT.Encodable where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show
