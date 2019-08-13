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
                 ( CofreeF (..), CofreeT (..) )
import qualified Data.Function as Function
import           Data.Functor.Identity
                 ( Identity (..) )
import           Numeric.Natural
                 ( Natural )

import qualified Kore.AllPath as AllPath
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Location as Attribute
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Pattern.Defined as Attribute.Pattern
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute
import qualified Kore.Attribute.Pattern.Function as Attribute.Pattern
import qualified Kore.Attribute.Pattern.Functional as Attribute.Pattern
import qualified Kore.Attribute.Source as Attribute
import           Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.Internal.MultiOr
import           Kore.Internal.Pattern
                 ( Conditional (..) )
import           Kore.Internal.TermLike as TermLike
import           Kore.OnePath.StrategyPattern
                 ( StrategyPattern )
import qualified Kore.OnePath.StrategyPattern as StrategyPattern
import           Kore.Predicate.Predicate
import           Kore.Proof.Functional
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import qualified Kore.Step.PatternAttributesError as PatternAttributesError
import           Kore.Step.Rule
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
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
import           Kore.Syntax as Syntax
import           Kore.Syntax.Sentence as Syntax
import           Kore.Unification.Error
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Target
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..), foldMapVariable )
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

instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    )
    => SumEqualWithExplanation (PatternF variable child)
  where
    sumConstructorPair (Syntax.AndF a1) (Syntax.AndF a2) =
        SumConstructorSameWithArguments (EqWrap "AndF" a1 a2)
    sumConstructorPair pattern1@(Syntax.AndF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.ApplicationF a1) (Syntax.ApplicationF a2) =
        SumConstructorSameWithArguments (EqWrap "ApplicationF" a1 a2)
    sumConstructorPair pattern1@(Syntax.ApplicationF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.BottomF a1) (Syntax.BottomF a2) =
        SumConstructorSameWithArguments (EqWrap "BottomF" a1 a2)
    sumConstructorPair pattern1@(Syntax.BottomF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.CeilF a1) (Syntax.CeilF a2) =
        SumConstructorSameWithArguments (EqWrap "CeilF" a1 a2)
    sumConstructorPair pattern1@(Syntax.CeilF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.DomainValueF a1) (Syntax.DomainValueF a2) =
        SumConstructorSameWithArguments (EqWrap "DomainValueF" a1 a2)
    sumConstructorPair pattern1@(Syntax.DomainValueF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.EqualsF a1) (Syntax.EqualsF a2) =
        SumConstructorSameWithArguments (EqWrap "EqualsF" a1 a2)
    sumConstructorPair pattern1@(Syntax.EqualsF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.ExistsF a1) (Syntax.ExistsF a2) =
        SumConstructorSameWithArguments (EqWrap "ExistsF" a1 a2)
    sumConstructorPair pattern1@(Syntax.ExistsF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.FloorF a1) (Syntax.FloorF a2) =
        SumConstructorSameWithArguments (EqWrap "FloorF" a1 a2)
    sumConstructorPair pattern1@(Syntax.FloorF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.ForallF a1) (Syntax.ForallF a2) =
        SumConstructorSameWithArguments (EqWrap "ForallF" a1 a2)
    sumConstructorPair pattern1@(Syntax.ForallF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.IffF a1) (Syntax.IffF a2) =
        SumConstructorSameWithArguments (EqWrap "IffF" a1 a2)
    sumConstructorPair pattern1@(Syntax.IffF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.ImpliesF a1) (Syntax.ImpliesF a2) =
        SumConstructorSameWithArguments (EqWrap "ImpliesF" a1 a2)
    sumConstructorPair pattern1@(Syntax.ImpliesF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.InF a1) (Syntax.InF a2) =
        SumConstructorSameWithArguments (EqWrap "InF" a1 a2)
    sumConstructorPair pattern1@(Syntax.InF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.MuF a1) (Syntax.MuF a2) =
        SumConstructorSameWithArguments (EqWrap "MuF" a1 a2)
    sumConstructorPair pattern1@(Syntax.MuF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.NextF a1) (Syntax.NextF a2) =
        SumConstructorSameWithArguments (EqWrap "NextF" a1 a2)
    sumConstructorPair pattern1@(Syntax.NextF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.NotF a1) (Syntax.NotF a2) =
        SumConstructorSameWithArguments (EqWrap "NotF" a1 a2)
    sumConstructorPair pattern1@(Syntax.NotF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.NuF a1) (Syntax.NuF a2) =
        SumConstructorSameWithArguments (EqWrap "NuF" a1 a2)
    sumConstructorPair pattern1@(Syntax.NuF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.OrF a1) (Syntax.OrF a2) =
        SumConstructorSameWithArguments (EqWrap "OrF" a1 a2)
    sumConstructorPair pattern1@(Syntax.OrF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.RewritesF a1) (Syntax.RewritesF a2) =
        SumConstructorSameWithArguments (EqWrap "RewritesF" a1 a2)
    sumConstructorPair pattern1@(Syntax.RewritesF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.StringLiteralF a1) (Syntax.StringLiteralF a2) =
        SumConstructorSameWithArguments (EqWrap "StringLiteralF" a1 a2)
    sumConstructorPair pattern1@(Syntax.StringLiteralF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.CharLiteralF a1) (Syntax.CharLiteralF a2) =
        SumConstructorSameWithArguments (EqWrap "CharLiteralF" a1 a2)
    sumConstructorPair pattern1@(Syntax.CharLiteralF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.TopF a1) (Syntax.TopF a2) =
        SumConstructorSameWithArguments (EqWrap "TopF" a1 a2)
    sumConstructorPair pattern1@(Syntax.TopF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.VariableF a1) (Syntax.VariableF a2) =
        SumConstructorSameWithArguments (EqWrap "VariableF" a1 a2)
    sumConstructorPair pattern1@(Syntax.VariableF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (Syntax.InhabitantF s1) (Syntax.InhabitantF s2) =
        SumConstructorSameWithArguments (EqWrap "InhabitantF" s1 s2)
    sumConstructorPair pattern1@(Syntax.InhabitantF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1)
            (printWithExplanation pattern2)

instance
    ( EqualWithExplanation child
    , Eq child, Eq variable
    , Show child
    , EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (TermLikeF variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Show variable
    , Eq variable
    , EqualWithExplanation variable
    ) =>
    EqualWithExplanation (TermLike variable)
  where
    compareWithExplanation a@(TermLike _) = wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    ( Show variable
    , Eq variable
    , EqualWithExplanation variable
    ) =>
    WrapperEqualWithExplanation (TermLike variable)
  where
    wrapperField expected actual =
        EqWrap
            "getTermLike = "
            (getTermLike expected)
            (getTermLike actual)
    wrapperConstructorName _ = "TermLike"

instance
    ( Show (Pattern variable annotation)
    , Show variable
    , Eq variable
    , EqualWithExplanation variable
    , Show annotation
    , Eq annotation
    , EqualWithExplanation annotation
    ) =>
    EqualWithExplanation (Pattern variable annotation)
  where
    compareWithExplanation a@(Pattern _) = wrapperCompareWithExplanation a
    printWithExplanation = show

instance
    ( Show (Pattern variable annotation)
    , Show variable
    , Eq variable
    , EqualWithExplanation variable
    , Show annotation
    , Eq annotation
    , EqualWithExplanation annotation
    ) =>
    WrapperEqualWithExplanation (Pattern variable annotation)
  where
    wrapperField expected actual =
        EqWrap
            "getPattern = "
            (getPattern expected)
            (getPattern actual)
    wrapperConstructorName _ = "Pattern"

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

instance
    ( Show head, EqualWithExplanation head
    , Show child, EqualWithExplanation child
    ) =>
    StructEqualWithExplanation (Application head child)
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

instance
    ( Show head, EqualWithExplanation head
    , Show child, EqualWithExplanation child
    ) =>
    EqualWithExplanation (Application head child)
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
    (Eq child, Show child) =>
    EqualWithExplanation (DomainValue Sort child)
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
    => StructEqualWithExplanation (Exists Sort variable child)
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
    ) => EqualWithExplanation (Exists Sort variable child)
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
    => StructEqualWithExplanation (Forall Sort variable child)
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
    ) => EqualWithExplanation (Forall Sort variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Show child
    , EqualWithExplanation child
    )
    => StructEqualWithExplanation (Iff Sort child)
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
    ) => EqualWithExplanation (Iff Sort child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Implies Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (In Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq child
    , Eq variable
    , Show child
    , Show variable
    , EqualWithExplanation child
    , EqualWithExplanation variable
    )
    => StructEqualWithExplanation (Mu variable child)
  where
    structFieldsWithNames
        expected@(Mu _ _)
        actual@(Mu _ _)
      = [ EqWrap
            "muVariable = "
            (muVariable expected)
            (muVariable actual)
        , EqWrap
            "muChild = "
            (muChild expected)
            (muChild actual)
        ]
    structConstructorName _ = "Mu"
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    ) => EqualWithExplanation (Mu variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Eq child, Show child)
    => EqualWithExplanation (Next Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance (Show child, Eq child, EqualWithExplanation child)
  =>
    StructEqualWithExplanation (Not Sort child)
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
    => EqualWithExplanation (Not Sort child)
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
    => StructEqualWithExplanation (Nu variable child)
  where
    structFieldsWithNames
        expected@(Nu _ _)
        actual@(Nu _ _)
      = [ EqWrap
            "nuVariable = "
            (nuVariable expected)
            (nuVariable actual)
        , EqWrap
            "nuChild = "
            (nuChild expected)
            (nuChild actual)
        ]
    structConstructorName _ = "Nu"
instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    ) => EqualWithExplanation (Nu variable child)
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
    => EqualWithExplanation (Rewrites Sort child)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation StringLiteral where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation CharLiteral where
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
    ) => SumEqualWithExplanation (ElementVariable variable)
  where
    sumConstructorPair (ElementVariable a1) (ElementVariable a2) =
        SumConstructorSameWithArguments
        $ EqWrap "ElementVariable" a1 a2

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (ElementVariable variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => SumEqualWithExplanation (SetVariable variable)
  where
    sumConstructorPair (SetVariable a1) (SetVariable a2) =
        SumConstructorSameWithArguments
        $ EqWrap "SetVariable" a1 a2

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (SetVariable variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation (Inhabitant child) where
    structFieldsWithNames expected@(Inhabitant _) actual =
        [ Function.on (EqWrap "inhSort = ") inhSort expected actual ]
    structConstructorName _ = "Inhabitant"

instance EqualWithExplanation (Inhabitant child) where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => SumEqualWithExplanation (UnifiedVariable variable)
  where
    sumConstructorPair (SetVar v1) (SetVar v2) =
        SumConstructorSameWithArguments
        $ EqWrap "ElemVar" v1 v2
    sumConstructorPair v1@(SetVar _) v2 =
        SumConstructorDifferent
            (printWithExplanation v1) (printWithExplanation v2)

    sumConstructorPair (ElemVar v1) (ElemVar v2) =
        SumConstructorSameWithArguments
        $ EqWrap "SetVar" v1 v2
    sumConstructorPair v1@(ElemVar _) v2 =
        SumConstructorDifferent
            (printWithExplanation v1) (printWithExplanation v2)

instance
    ( EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (UnifiedVariable variable)
  where
    compareWithExplanation = sumCompareWithExplanation
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

instance StructEqualWithExplanation TermLike.Alias where
    structFieldsWithNames
        expected@(TermLike.Alias _ _ _)
        actual@(TermLike.Alias _ _ _)
      =
        [ Function.on (EqWrap "aliasConstructor = ")
            TermLike.aliasConstructor expected actual
        , Function.on (EqWrap "aliasParams = ")
            TermLike.aliasParams expected actual
        ]
    structConstructorName _ = "Alias"

instance EqualWithExplanation TermLike.Alias where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation TermLike.Symbol where
    structFieldsWithNames
        expected@(TermLike.Symbol _ _ _ _)
        actual@(TermLike.Symbol _ _ _ _)
      =
        [ Function.on (EqWrap "symbolConstructor = ")
            TermLike.symbolConstructor expected actual
        , Function.on (EqWrap "symbolParams = ")
            TermLike.symbolParams expected actual
        ]
    structConstructorName _ = "Symbol"

instance EqualWithExplanation TermLike.Symbol where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation SymbolOrAlias where
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

instance EqualWithExplanation SymbolOrAlias where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation UnificationError where
    sumConstructorPair (UnsupportedPatterns a1) (UnsupportedPatterns a2) =
        SumConstructorSameWithArguments
        $ EqWrap "UnsupportedPatterns" a1 a2

instance EqualWithExplanation UnificationError where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation SubstitutionError where
    sumConstructorPair
        (NonCtorCircularVariableDependency a1)
        (NonCtorCircularVariableDependency a2)
      =
        SumConstructorSameWithArguments
        $ EqWrap "NonCtorCircularVariableDependency"
            (foldMapVariable toVariable <$> a1)
            (foldMapVariable toVariable <$> a2)


instance EqualWithExplanation SubstitutionError where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq variable
    , Show variable
    )
    => EqualWithExplanation (FunctionalProof variable)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance
    ( Eq variable
    , Show variable
    )
    => EqualWithExplanation (FunctionProof variable)
  where
    compareWithExplanation = rawCompareWithExplanation
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
    ( Show variable , Ord variable , EqualWithExplanation variable )
    => EqualWithExplanation (Substitution variable)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    EqualWithExplanation (Domain.Builtin key child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

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

instance EqualWithExplanation InternalString where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation InternalString where
    structFieldsWithNames expect actual =
        [ Function.on (EqWrap "internalStringSort = ") internalStringSort expect actual
        , Function.on (EqWrap "internalStringValue = ") internalStringValue expect actual
        ]
    structConstructorName _ = "InternalString"

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
    structFieldsWithNames expect actual@(InternalList _ _ _ _ _) =
        [ Function.on
            (EqWrap "builtinListSort = ") builtinListSort expect actual
        , Function.on
            (EqWrap "builtinListUnit = ") builtinListUnit expect actual
        , Function.on
            (EqWrap "builtinListElement = ") builtinListElement expect actual
        , Function.on
            (EqWrap "builtinListConcat = ") builtinListConcat expect actual
        , Function.on
            (EqWrap "builtinListChild = ") builtinListChild expect actual
        ]
    structConstructorName _ = "InternalList"

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation (normalized key child), Show (normalized key child)
    , EqualWithExplanation child, Show child
    ) =>
    EqualWithExplanation (InternalAc key normalized child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation (normalized key child), Show (normalized key child)
    , EqualWithExplanation child, Show child
    ) =>
    StructEqualWithExplanation (InternalAc key normalized child)
  where
    structFieldsWithNames expect actual@(InternalAc _ _ _ _ _) =
        [ Function.on (EqWrap "builtinAcSort = ") builtinAcSort expect actual
        , Function.on (EqWrap "builtinAcUnit = ") builtinAcUnit expect actual
        , Function.on
            (EqWrap "builtinAcElement = ") builtinAcElement expect actual
        , Function.on
            (EqWrap "builtinAcConcat = ") builtinAcConcat expect actual
        , Function.on
            (EqWrap "builtinAcChild = ") builtinAcChild expect actual
        ]
    structConstructorName _ = "InternalAc"

instance
    (EqualWithExplanation child, Show child) =>
    WrapperEqualWithExplanation (SetElement child)
  where
    wrapperConstructorName _ = "SetElement"
    wrapperField = Function.on (EqWrap "getSetElement = ") getSetElement

instance (EqualWithExplanation child, Show child)
    => EqualWithExplanation (SetElement child)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation (SetValue child) where
    sumConstructorPair SetValue SetValue =
        SumConstructorSameNoArguments

instance EqualWithExplanation (SetValue child) where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    SumEqualWithExplanation (NormalizedSet key child)
  where
    sumConstructorPair (NormalizedSet a1) (NormalizedSet a2) =
        SumConstructorSameWithArguments
            (EqWrap "NormalizedSet" a1 a2)

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    EqualWithExplanation (NormalizedSet key child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    WrapperEqualWithExplanation (MapElement child)
  where
    wrapperConstructorName _ = "MapElement"
    wrapperField = Function.on (EqWrap "getMapElement = ") getMapElement

instance (EqualWithExplanation child, Show child)
    => EqualWithExplanation (MapElement child)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance (EqualWithExplanation child, Show child)
    => SumEqualWithExplanation (MapValue child)
  where
    sumConstructorPair (MapValue a1) (MapValue a2) =
        SumConstructorSameWithArguments
            (EqWrap "MapValue" a1 a2)

instance (EqualWithExplanation child, Show child)
    => EqualWithExplanation (MapValue child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    SumEqualWithExplanation (NormalizedMap key child)
  where
    sumConstructorPair (NormalizedMap a1) (NormalizedMap a2) =
        SumConstructorSameWithArguments
            (EqWrap "NormalizedMap" a1 a2)

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    EqualWithExplanation (NormalizedMap key child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    , EqualWithExplanation (Element collection child)
    , Show (Element collection child)
    , EqualWithExplanation (Value collection child)
    , Show (Value collection child)
    ) =>
    EqualWithExplanation (NormalizedAc collection key child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    , EqualWithExplanation (Element collection child)
    , Show (Element collection child)
    , EqualWithExplanation (Value collection child)
    , Show (Value collection child)
    ) =>
    StructEqualWithExplanation (NormalizedAc collection key child)
  where
    structFieldsWithNames expect actual@(NormalizedAc _ _ _) =
        [ Function.on
            (EqWrap "elementsWithVariables = ")
            elementsWithVariables
            expect
            actual
        , Function.on
            (EqWrap "concreteElements = ") concreteElements expect actual
        , Function.on (EqWrap "opaque = ") opaque expect actual
        ]
    structConstructorName _ = "NormalizedAc"

instance
    ( EqualWithExplanation key, Show key
    , EqualWithExplanation child, Show child
    ) =>
    SumEqualWithExplanation (Domain.Builtin key child)
  where
    sumConstructorPair (BuiltinInt int1) (BuiltinInt int2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinInt" int1 int2)
    sumConstructorPair (BuiltinBool bool1) (BuiltinBool bool2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinBool" bool1 bool2)
    sumConstructorPair (BuiltinString string1) (BuiltinString string2) =
        SumConstructorSameWithArguments
            (EqWrap "BuiltinString" string1 string2)
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
    ( EqualWithExplanation variable , Show variable , Ord variable )
    => SumEqualWithExplanation (Substitution variable)
  where
    sumConstructorPair s1 s2 =
        SumConstructorSameWithArguments
            (EqWrap "Substitution" s1Inner s2Inner)
      where
        s1Inner = Substitution.unwrap s1
        s2Inner = Substitution.unwrap s2

instance
    ( Show variable, Show child , Ord variable
    , EqualWithExplanation variable
    , EqualWithExplanation child
    , EqualWithExplanation (TermLike variable)
    )
    => StructEqualWithExplanation (Conditional variable child)
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
    ( Show variable, Show child , Ord variable
    , EqualWithExplanation variable
    , EqualWithExplanation child
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (Conditional variable child)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( EqualWithExplanation variable
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
    ( Show variable
    , Ord variable
    , EqualWithExplanation variable
    )
    => StructEqualWithExplanation (AttemptedAxiomResults variable)
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
    ( Show variable , Ord variable , EqualWithExplanation variable )
    => EqualWithExplanation (AttemptedAxiomResults variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Show variable , Ord variable , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => SumEqualWithExplanation (AttemptedAxiom variable)
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
    ( Show variable , Ord variable , EqualWithExplanation variable
    , EqualWithExplanation (TermLike variable)
    )
    => EqualWithExplanation (AttemptedAxiom variable)
  where
    compareWithExplanation = sumCompareWithExplanation
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

instance EqualWithExplanation PatternAttributesError.FunctionError where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation PatternAttributesError.FunctionalError where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation UnificationOrSubstitutionError where
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

instance EqualWithExplanation UnificationOrSubstitutionError where
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

instance EqualWithExplanation Attribute.Null where
    compareWithExplanation _ _ = Nothing
    printWithExplanation = show

instance
    ( EqualWithExplanation variable, Show variable
    ) => StructEqualWithExplanation (Attribute.Pattern variable)
  where
    structFieldsWithNames
        expected@(Attribute.Pattern _ _ _ _ _)
        actual@(Attribute.Pattern _ _ _ _ _)
      =
        [ EqWrap
            "patternSort = "
            (Attribute.patternSort expected)
            (Attribute.patternSort actual)
        , EqWrap
            "freeVariables = "
            (Attribute.freeVariables expected)
            (Attribute.freeVariables actual)
        , EqWrap
            "functional = "
            (Attribute.functional expected)
            (Attribute.functional actual)
        , EqWrap
            "function = "
            (Attribute.function expected)
            (Attribute.function actual)
        , EqWrap
            "defined = "
            (Attribute.defined expected)
            (Attribute.defined actual)
        ]
    structConstructorName _ = "Pattern"

instance
    (EqualWithExplanation variable, Show variable) =>
    EqualWithExplanation (Attribute.FreeVariables variable)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation variable, Show variable) =>
    WrapperEqualWithExplanation (Attribute.FreeVariables variable)
  where
    wrapperConstructorName _ = "FreeVariables"
    wrapperField =
        Function.on (EqWrap "getFreeVariables = ") Attribute.getFreeVariables

instance EqualWithExplanation Attribute.Pattern.Functional where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Pattern.Functional where
    wrapperConstructorName _ = "Functional"
    wrapperField =
        Function.on (EqWrap "isFunctional = ") Attribute.Pattern.isFunctional

instance EqualWithExplanation Attribute.Pattern.Function where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Pattern.Function where
    wrapperConstructorName _ = "Function"
    wrapperField =
        Function.on (EqWrap "isFunction = ") Attribute.Pattern.isFunction

instance EqualWithExplanation Attribute.Pattern.Defined where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance WrapperEqualWithExplanation Attribute.Pattern.Defined where
    wrapperConstructorName _ = "Defined"
    wrapperField =
        Function.on (EqWrap "isDefined = ") Attribute.Pattern.isDefined

instance
    ( EqualWithExplanation variable, Show variable
    ) => EqualWithExplanation (Attribute.Pattern variable)
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


instance SumEqualWithExplanation AxiomIdentifier where
    sumConstructorPair
        (AxiomIdentifier.Application p1) (AxiomIdentifier.Application p2)
      =
        SumConstructorSameWithArguments (EqWrap "Application" p1 p2)
    sumConstructorPair
        (AxiomIdentifier.Ceil p1) (AxiomIdentifier.Ceil p2)
      =
        SumConstructorSameWithArguments (EqWrap "Ceil" p1 p2)
    sumConstructorPair
        (AxiomIdentifier.Equals p1 q1) (AxiomIdentifier.Equals p2 q2)
      =
        SumConstructorSameWithArguments (EqWrap "Equals" (p1, q1) (p2, q2))
    sumConstructorPair
        (AxiomIdentifier.Exists p1) (AxiomIdentifier.Exists p2)
      =
        SumConstructorSameWithArguments (EqWrap "Exists" p1 p2)
    sumConstructorPair AxiomIdentifier.Variable AxiomIdentifier.Variable =
        SumConstructorSameNoArguments
    sumConstructorPair p1 p2 =
        SumConstructorDifferent
            (printWithExplanation p1)
            (printWithExplanation p2)

instance EqualWithExplanation AxiomIdentifier where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    ( Ord  variable
    , Show variable
    , EqualWithExplanation variable
    ) =>
    EqualWithExplanation (RulePattern variable)
  where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance
    ( Ord  variable
    , Show variable
    , EqualWithExplanation variable
    ) =>
    StructEqualWithExplanation (RulePattern variable)
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

instance EqualWithExplanation Syntax.Alias where
    compareWithExplanation = structCompareWithExplanation
    printWithExplanation = show

instance StructEqualWithExplanation Syntax.Alias where
    structConstructorName _ = "Alias"
    structFieldsWithNames expect@(Syntax.Alias _ _) actual@(Syntax.Alias _ _) =
        map (\f -> f expect actual)
            [ Function.on (EqWrap "aliasConstructor = ") Syntax.aliasConstructor
            , Function.on (EqWrap "aliasParams = ") Syntax.aliasParams
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

instance
    ( EqualWithExplanation child
    , Eq child
    , Show child
    , EqualWithExplanation variable
    , Eq variable
    , Show variable
    )
    => SumEqualWithExplanation (TermLikeF variable child)
  where
    sumConstructorPair (TermLike.AndF a1) (TermLike.AndF a2) =
        SumConstructorSameWithArguments (EqWrap "AndF" a1 a2)
    sumConstructorPair pattern1@(TermLike.AndF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.ApplyAliasF a1) (TermLike.ApplyAliasF a2) =
        SumConstructorSameWithArguments (EqWrap "ApplyAliasF" a1 a2)
    sumConstructorPair pattern1@(TermLike.ApplyAliasF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.ApplySymbolF a1) (TermLike.ApplySymbolF a2) =
        SumConstructorSameWithArguments (EqWrap "ApplySymbolF" a1 a2)
    sumConstructorPair pattern1@(TermLike.ApplySymbolF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.BottomF a1) (TermLike.BottomF a2) =
        SumConstructorSameWithArguments (EqWrap "BottomF" a1 a2)
    sumConstructorPair pattern1@(TermLike.BottomF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.BuiltinF a1) (TermLike.BuiltinF a2) =
        SumConstructorSameWithArguments (EqWrap "BuiltinF" a1 a2)
    sumConstructorPair pattern1@(TermLike.BuiltinF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.CeilF a1) (TermLike.CeilF a2) =
        SumConstructorSameWithArguments (EqWrap "CeilF" a1 a2)
    sumConstructorPair pattern1@(TermLike.CeilF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.DomainValueF a1) (TermLike.DomainValueF a2) =
        SumConstructorSameWithArguments (EqWrap "DomainValueF" a1 a2)
    sumConstructorPair pattern1@(TermLike.DomainValueF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.EqualsF a1) (TermLike.EqualsF a2) =
        SumConstructorSameWithArguments (EqWrap "EqualsF" a1 a2)
    sumConstructorPair pattern1@(TermLike.EqualsF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.ExistsF a1) (TermLike.ExistsF a2) =
        SumConstructorSameWithArguments (EqWrap "ExistsF" a1 a2)
    sumConstructorPair pattern1@(TermLike.ExistsF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.FloorF a1) (TermLike.FloorF a2) =
        SumConstructorSameWithArguments (EqWrap "FloorF" a1 a2)
    sumConstructorPair pattern1@(TermLike.FloorF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.ForallF a1) (TermLike.ForallF a2) =
        SumConstructorSameWithArguments (EqWrap "ForallF" a1 a2)
    sumConstructorPair pattern1@(TermLike.ForallF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.IffF a1) (TermLike.IffF a2) =
        SumConstructorSameWithArguments (EqWrap "IffF" a1 a2)
    sumConstructorPair pattern1@(TermLike.IffF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.ImpliesF a1) (TermLike.ImpliesF a2) =
        SumConstructorSameWithArguments (EqWrap "ImpliesF" a1 a2)
    sumConstructorPair pattern1@(TermLike.ImpliesF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.InF a1) (TermLike.InF a2) =
        SumConstructorSameWithArguments (EqWrap "InF" a1 a2)
    sumConstructorPair pattern1@(TermLike.InF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.MuF a1) (TermLike.MuF a2) =
        SumConstructorSameWithArguments (EqWrap "MuF" a1 a2)
    sumConstructorPair pattern1@(TermLike.MuF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.NextF a1) (TermLike.NextF a2) =
        SumConstructorSameWithArguments (EqWrap "NextF" a1 a2)
    sumConstructorPair pattern1@(TermLike.NextF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.NotF a1) (TermLike.NotF a2) =
        SumConstructorSameWithArguments (EqWrap "NotF" a1 a2)
    sumConstructorPair pattern1@(TermLike.NotF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.NuF a1) (TermLike.NuF a2) =
        SumConstructorSameWithArguments (EqWrap "NuF" a1 a2)
    sumConstructorPair pattern1@(TermLike.NuF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.OrF a1) (TermLike.OrF a2) =
        SumConstructorSameWithArguments (EqWrap "OrF" a1 a2)
    sumConstructorPair pattern1@(TermLike.OrF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.RewritesF a1) (TermLike.RewritesF a2) =
        SumConstructorSameWithArguments (EqWrap "RewritesF" a1 a2)
    sumConstructorPair pattern1@(TermLike.RewritesF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.StringLiteralF a1) (TermLike.StringLiteralF a2) =
        SumConstructorSameWithArguments (EqWrap "StringLiteralF" a1 a2)
    sumConstructorPair pattern1@(TermLike.StringLiteralF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.CharLiteralF a1) (TermLike.CharLiteralF a2) =
        SumConstructorSameWithArguments (EqWrap "CharLiteralF" a1 a2)
    sumConstructorPair pattern1@(TermLike.CharLiteralF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.TopF a1) (TermLike.TopF a2) =
        SumConstructorSameWithArguments (EqWrap "TopF" a1 a2)
    sumConstructorPair pattern1@(TermLike.TopF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.VariableF a1) (TermLike.VariableF a2) =
        SumConstructorSameWithArguments (EqWrap "VariableF" a1 a2)
    sumConstructorPair pattern1@(TermLike.VariableF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

    sumConstructorPair (TermLike.InhabitantF s1) (TermLike.InhabitantF s2) =
        SumConstructorSameWithArguments (EqWrap "InhabitantF" s1 s2)
    sumConstructorPair pattern1@(TermLike.InhabitantF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1)
            (printWithExplanation pattern2)

    sumConstructorPair (TermLike.EvaluatedF a1) (TermLike.EvaluatedF a2) =
        SumConstructorSameWithArguments (EqWrap "EvaluatedF" a1 a2)
    sumConstructorPair pattern1@(TermLike.EvaluatedF _) pattern2 =
        SumConstructorDifferent
            (printWithExplanation pattern1) (printWithExplanation pattern2)

instance
    ( EqualWithExplanation child
    , Eq child, Eq variable
    , Show child
    , EqualWithExplanation variable
    , Show variable
    ) => EqualWithExplanation (PatternF variable child)
  where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    EqualWithExplanation (TermLike.Evaluated child)
  where
    compareWithExplanation = wrapperCompareWithExplanation
    printWithExplanation = show

instance
    (EqualWithExplanation child, Show child) =>
    WrapperEqualWithExplanation (TermLike.Evaluated child)
  where
    wrapperField = Function.on (EqWrap "getEvaluated = ") getEvaluated
    wrapperConstructorName _ = "Evaluated"
