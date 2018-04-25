{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MonoLocalBinds        #-}
 -- to avoid warnings that constraints (AsAst UnifiedPattern p) can be simplified
module Kore.MatchingLogic.ProofSystem.ProofAssistantTest
    (proofAssistantTests) where

import           Test.Tasty                                   (TestTree,
                                                               testGroup)
import           Test.Tasty.HUnit                             (assertFailure,
                                                               testCase)

import           Data.Kore.AST.Common                         (Application (..),
                                                               Attributes (..),
                                                               Definition (..),
                                                               Id (..), Meta,
                                                               Module (..),
                                                               ModuleName (..),
                                                               Pattern (..),
                                                               Sentence (..),
                                                               SentenceSymbol (..),
                                                               Sort (..),
                                                               Symbol (..),
                                                               SymbolOrAlias (..),
                                                               Variable)
import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.DefinitionVerifier     (AttributesVerification (..),
                                                               verifyAndIndexDefinition)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.MetaML.AST                         (MetaMLPattern)
import           Data.Kore.MetaML.MetaToKore

import           Kore.MatchingLogic.Error
import           Kore.MatchingLogic.HilbertProof              as HilbertProof (Proof (..),
                                                                               add,
                                                                               derive,
                                                                               emptyProof)
import           Kore.MatchingLogic.ProofSystem.Minimal       (MLRule (..), SubstitutedVariable (..),
                                                               SubstitutingVariable (..))
import           Kore.MatchingLogic.ProofSystem.MLProofSystem as MLProofSystem

import           Control.Monad                                (foldM)
import           Data.List                                    (foldl')
import qualified Data.Map.Strict                              as Map
import           Data.Text.Prettyprint.Doc

proofAssistantTests :: TestTree
proofAssistantTests =
    testGroup "MLProof Assistant"
        [ proposition1Tests
        , proposition2Tests
        , proposition3Tests
        , modusPonensTests
        , generalizationTests
        , variableSubstitutionTests
        , forallTests
        , propagateOrTests
        , propagateExistsTests
        , framingTests
        , existenceTests
        , singletonVariableTests
        , runTestScript
            "Simple MLProof for phi implies phi."
            [ testAddGoal
                (metaImplies phiSort phi (metaImplies phiSort phi phi))
                (NewGoalId 2)
            , testAddGoal
                (metaImplies phiSort
                    phi
                    (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                )
                (NewGoalId 4)
            , testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort phi
                        (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                    )
                    (metaImplies phiSort
                        (metaImplies phiSort phi (metaImplies phiSort phi phi))
                        (metaImplies phiSort phi phi)
                    )
                )
                (NewGoalId 5)
            , testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort phi (metaImplies phiSort phi phi))
                    (metaImplies phiSort phi phi)
                )
                (NewGoalId 3)
            , testAddGoal (metaImplies phiSort phi phi) (NewGoalId 1)

            , assertGoalCount 5
            , assertGoal (GoalId 1) (metaImplies phiSort phi phi)
            , assertGoal
                (GoalId 2)
                (metaImplies phiSort phi (metaImplies phiSort phi phi))
            , assertGoal (GoalId 3)
                (metaImplies phiSort
                    (metaImplies phiSort phi (metaImplies phiSort phi phi))
                    (metaImplies phiSort phi phi)
                )
            , assertGoal (GoalId 4)
                (metaImplies phiSort
                    phi
                    (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                )
            , assertGoal (GoalId 5)
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi
                        (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                    )
                    (metaImplies phiSort
                        (metaImplies phiSort phi (metaImplies phiSort phi phi))
                        (metaImplies phiSort phi phi)
                    )
                )

            , assertUnproven (GoalId 1)
            , assertUnproven (GoalId 2)
            , assertUnproven (GoalId 3)
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)

            , testModusPonens
                (GoalId 2)
                (GoalId 3)
                (GoalId 1)
            , assertGoalCount 5
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertUnproven (GoalId 3)
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)

            , testModusPonens
                (GoalId 4)
                (GoalId 5)
                (GoalId 3)
            , assertGoalCount 5
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertPartlyProven (GoalId 3) (GoalNeeds [GoalId 5, GoalId 4])
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)

            , testProposition2 phi (metaImplies phiSort phi phi) phi (GoalId 5)
            , assertGoalCount 5
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertPartlyProven (GoalId 3) (GoalNeeds [GoalId 4])
            , assertUnproven (GoalId 4)
            , assertProven (GoalId 5)

            , testProposition1 phi (metaImplies phiSort phi phi) (GoalId 4)
            , assertGoalCount 5
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 2])
            , assertUnproven (GoalId 2)
            , assertProven (GoalId 3)
            , assertProven (GoalId 4)
            , assertProven (GoalId 5)

            , testProposition1 phi phi (GoalId 2)
            , assertGoalCount 5
            , assertProven (GoalId 1)
            , assertProven (GoalId 2)
            , assertProven (GoalId 3)
            , assertProven (GoalId 4)
            , assertProven (GoalId 5)
            ]
        ]

x :: MetaVariable MetaSortVariable1
x = metaVariable "#x" xSort

y :: MetaVariable MetaSortVariable1
y = metaVariable "#y" xSort

z :: MetaVariable MetaSortVariable1
z = metaVariable "#z" xSort

xSort :: MetaSortVariable1
xSort = MetaSortVariable1 "#xsort"

phi :: MetaVariable CharListSort
phi = metaVariable "#phi" phiSort

phi' :: MetaVariable CharListSort
phi' = metaVariable "#phi'" phiSort

phi1 :: MetaVariable CharListSort
phi1 = metaVariable "#phi1" phiSort

phi2 :: MetaVariable CharListSort
phi2 = metaVariable "#phi2" phiSort

phi3 :: MetaVariable CharListSort
phi3 = metaVariable "#phi3" phiSort

psi :: MetaVariable CharListSort
psi = metaVariable "#psi" phiSort

psi1 :: MetaVariable CharListSort
psi1 = metaVariable "#psi1" phiSort

thingEqualsThing
    :: (MetaSort s, MetaPattern s p) => s -> p -> MetaEquals s p p CharListSort
thingEqualsThing sort thing =
    metaEquals (ResultSort phiSort) sort thing thing
xEqualsX
    :: MetaEquals
        MetaSortVariable1
        (MetaVariable MetaSortVariable1)
        (MetaVariable MetaSortVariable1)
        CharListSort
xEqualsX = thingEqualsThing xSort x
phiSort :: CharListSort
phiSort = CharListSort

-- phi -> (psi -> phi)
proposition1Tests :: TestTree
proposition1Tests =
    testGroup "Proposition1 tests"
        [ runTestScript "Fails if phi not matched on the first instance"
            [ testAddGoal
                (metaImplies phiSort qphi' (metaImplies phiSort qpsi qphi))
                (NewGoalId 1)
            , expectFailure
                (testProposition1 qphi qpsi (GoalId 1))
            ]
        , runTestScript "Fails if phi not matched on the second instance"
            [ testAddGoal
                (metaImplies phiSort qphi (metaImplies phiSort qpsi qphi'))
                (NewGoalId 1)
            , expectFailure
                (testProposition1 qphi qpsi (GoalId 1))
            ]
        , runTestScript "Fails if psi not matched"
            [ testAddGoal
                ( metaImplies phiSort
                    qphi
                    (metaImplies phiSort (metaImplies phiSort qphi qphi) qphi)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition1 qphi qpsi (GoalId 1))
            ]
        , runTestScript "Fails with incompatible sorts"
            [ testAddGoal
                ( metaImplies phiSort
                    qphi
                    (metaImplies phiSort (metaImplies phiSort qphi qphi) qphi)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition1 qphi qpsiS (GoalId 1))
            ]
        , runTestScript "No alpha renaming for free variables"
            [ testAddGoal
                (metaImplies phiSort qphi (metaImplies phiSort phi' qphi))
                (NewGoalId 1)
            , expectFailure
                (testProposition1 qphi psi (GoalId 1))
            ]
        , runTestScript "Infers proposition"
            [ testAddGoal
                (metaImplies phiSort phi (metaImplies phiSort psi phi))
                (NewGoalId 1)
            , testProposition1 phi psi (GoalId 1)
            ]
        ]
  where
    psip = metaVariable "#psi" psiSort
    qphi = metaExists phiSort phi phi
    qpsi = metaExists phiSort psi psi
    qpsiS = metaExists psiSort psi psip
    qphi' = metaExists phiSort phi' phi'
    psiSort = MetaSortVariable1 "#s2"

-- (phi1 -> (phi2 -> phi3)) -> (phi1 -> phi2) -> (phi1 -> phi3)
proposition2Tests :: TestTree
proposition2Tests =
    testGroup "Proposition2 tests"
        [ runTestScript "Fails if phi1 is not matched on the first instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        psi
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi1 is not matched on the second instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort psi phi2)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi1 is not matched on the third instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort psi phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi2 is not matched on the first instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort psi phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi2 is not matched on the second instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 psi)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi3 is not matched on the first instance."
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 psi))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Fails if phi3 not matched on the second instance"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort phi1 psi)
                    )
                )
               (NewGoalId 1)
            , expectFailure
                (testProposition2 phi1 phi2 phi3 (GoalId 1))
            ]
        , runTestScript "Infers proposition"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi1
                        (metaImplies phiSort phi2 phi3))
                    (metaImplies phiSort
                        (metaImplies phiSort phi1 phi2)
                        (metaImplies phiSort phi1 phi3)
                    )
                )
               (NewGoalId 1)
            , testProposition2 phi1 phi2 phi3 (GoalId 1)
            ]
        ]

-- (not phi1 -> not phi2) -> (phi2 -> phi1)
proposition3Tests :: TestTree
proposition3Tests =
    testGroup "Proposition3 tests"
        [ runTestScript "Fails if phi1 not matched on the first instance"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        (metaNot phiSort psi)
                        (metaNot phiSort phi2)
                    )
                    (metaImplies phiSort phi2 phi1)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition3 phi1 phi2 (GoalId 1))
            ]
        , runTestScript "Fails if phi1 not matched on the second instance"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        (metaNot phiSort phi1)
                        (metaNot phiSort phi2)
                    )
                    (metaImplies phiSort phi2 psi)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition3 phi1 phi2 (GoalId 1))
            ]
        , runTestScript "Fails if phi2 not matched on the first instance"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        (metaNot phiSort phi1)
                        (metaNot phiSort psi)
                    )
                    (metaImplies phiSort phi2 phi1)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition3 phi1 phi2 (GoalId 1))
            ]
        , runTestScript "Fails if phi2 not matched on the second instance"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        (metaNot phiSort phi1)
                        (metaNot phiSort phi2)
                    )
                    (metaImplies phiSort psi phi1)
                )
                (NewGoalId 1)
            , expectFailure
                (testProposition3 phi1 phi2 (GoalId 1))
            ]
        , runTestScript "Infers proposition"
            [ testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort
                        (metaNot phiSort phi1)
                        (metaNot phiSort phi2)
                    )
                    (metaImplies phiSort phi2 phi1)
                )
                (NewGoalId 1)
            , testProposition3 phi1 phi2 (GoalId 1)
            ]
        ]

-- from phi1 and (phi1 -> phi2), get phi2
modusPonensTests :: TestTree
modusPonensTests =
    testGroup "Modus Ponens tests"
        [ runTestScript "Fails if phi1 not matched"
            [ testAddGoal psi (NewGoalId 1)
            , testAddGoal (metaImplies phiSort phi1 phi2) (NewGoalId 2)
            , testAddGoal phi2 (NewGoalId 3)
            , expectFailure
                (testModusPonens (GoalId 1) (GoalId 2) (GoalId 3))
            ]
        , runTestScript "Fails if phi2 not matched"
            [ testAddGoal phi1 (NewGoalId 1)
            , testAddGoal (metaImplies phiSort phi1 phi2) (NewGoalId 2)
            , testAddGoal psi (NewGoalId 3)
            , expectFailure
                (testModusPonens (GoalId 1) (GoalId 2) (GoalId 3))
            ]
        , runTestScript "Fails if propositions are reversed"
            [ testAddGoal phi1 (NewGoalId 1)
            , testAddGoal (metaImplies phiSort phi1 phi2) (NewGoalId 2)
            , testAddGoal phi2 (NewGoalId 3)
            , expectFailure
                (testModusPonens (GoalId 2) (GoalId 1) (GoalId 3))
            ]
        , runTestScript "Infers formula"
            [ testAddGoal phi1 (NewGoalId 1)
            , testAddGoal (metaImplies phiSort phi1 phi2) (NewGoalId 2)
            , testAddGoal phi2 (NewGoalId 3)
            , testModusPonens (GoalId 1) (GoalId 2) (GoalId 3)
            ]
        ]

generalizationTests :: TestTree
generalizationTests =
    testGroup "Generalization tests"
        [ runTestScript "Fails if the patterns do not match"
            [ testAddGoal z (NewGoalId 1)
            , testAddGoal (metaForall xSort x y) (NewGoalId 2)
            , expectFailure
                (testGeneralization
                    x
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Fails if the variables does not match"
            [ testAddGoal y (NewGoalId 1)
            , testAddGoal (metaForall xSort x y) (NewGoalId 2)
            , expectFailure
                (testGeneralization
                    z
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Infers formula"
            [ testAddGoal y (NewGoalId 1)
            , testAddGoal (metaForall xSort x y) (NewGoalId 2)
            , testGeneralization
                x
                (GoalId 1)
                (GoalId 2)
            ]
        , runTestScript "Infers formula with free variable generalization"
            [ testAddGoal x (NewGoalId 1)
            , testAddGoal (metaForall xSort x x) (NewGoalId 2)
            , testGeneralization
                x
                (GoalId 1)
                (GoalId 2)
            ]
        ]

-- (forall x . P) -> P[y/x]
variableSubstitutionTests :: TestTree
variableSubstitutionTests =
    testGroup "Variable Substitution tests"
        [ runTestScript "Fails if the wrong variable is substituted"
            [ testAddGoal
                (metaImplies xSort (metaForall xSort x x) y) (NewGoalId 1)
            , expectFailure
                (testVariableSubstitution
                    (SubstitutingVariable (asMetaVariable y))
                    (SubstitutedVariable (asMetaVariable z))
                    x
                    (GoalId 1))
            ]
        , runTestScript "Fails when substituting with the wrong variable"
            [ testAddGoal
                (metaImplies xSort (metaForall xSort x x) y) (NewGoalId 1)
            , expectFailure
                (testVariableSubstitution
                    (SubstitutingVariable (asMetaVariable z))
                    (SubstitutedVariable (asMetaVariable x))
                    x
                    (GoalId 1))
            ]
        , runTestScript "Fails when capturing a variable"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x
                        (metaForall xSort y
                            (metaImplies xSort x y)
                        )
                    )
                    (metaForall xSort y (metaImplies xSort y y))
                )
                (NewGoalId 1)
            , expectFailure
                (testVariableSubstitution
                    (SubstitutingVariable (asMetaVariable y))
                    (SubstitutedVariable (asMetaVariable x))
                    (metaForall xSort y (metaImplies xSort x y))
                    (GoalId 1))
            ]
        , runTestScript "Infers formula"
            [ testAddGoal
                (metaImplies xSort (metaForall xSort x x) y) (NewGoalId 1)
            , testVariableSubstitution
                (SubstitutingVariable (asMetaVariable y))
                (SubstitutedVariable (asMetaVariable x))
                x
                (GoalId 1)
            ]
        ]

-- (forall x . (phi1 -> phi2)) -> (phi1 -> forall x.phi2)
-- if x does not occur free in phi1
forallTests :: TestTree
forallTests =
    testGroup "Forall tests"
        [ runTestScript "Fails when variable not matched 1"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    z y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when variable not matched 2"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort z (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when variable not matched 3"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort z x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi1 not matched 1"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x z x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi1 not matched 2"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort z x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi1 not matched 3"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort z (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi2 not matched 1"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y z
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi2 not matched 2"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y z))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when phi2 not matched 3"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x z))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x y x
                    (GoalId 1)
                )
            ]
        , runTestScript "Fails when x free in phi1"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort x x))
                    (metaImplies xSort x (metaForall xSort x x))
                )
                (NewGoalId 1)
            , expectFailure
                (testForall
                    x x x
                    (GoalId 1)
                )
            ]
        , runTestScript "Succeeds"
            [ testAddGoal
                (metaImplies xSort
                    (metaForall xSort x (metaImplies xSort y x))
                    (metaImplies xSort y (metaForall xSort x x))
                )
                (NewGoalId 1)
            , testForall
                x y x
                (GoalId 1)
            ]
        , let
            qx = metaForall xSort x x
          in
            runTestScript "Succeeds when x quantified in phi1"
                [ testAddGoal
                    (metaImplies xSort
                        (metaForall xSort x (metaImplies xSort qx x))
                        (metaImplies xSort qx (metaForall xSort x x))
                    )
                    (NewGoalId 1)
                , testForall
                    x qx x
                    (GoalId 1)
                ]
        ]

data MetaSigma s p1 p2 p3 = MetaSigma
    { metaSigmaSort   :: s
    , metaSigmaFirst  :: p1
    , metaSigmaSecond :: p2
    , metaSigmaThird  :: p3
    }
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2, MetaPattern s p3)
    => ProperPattern Meta s (MetaSigma s p1 p2 p3)
  where
    asProperPattern (MetaSigma _ p1 p2 p3) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = sigmaSymbol
            , applicationChildren = [asAst p1, asAst p2, asAst p3]
            }
metaSigma
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2, MetaPattern s p3)
    => s -> p1 -> p2 -> p3 -> MetaSigma s p1 p2 p3
metaSigma = MetaSigma

sigma2
    :: MetaPattern CharListSort p1
    => p1
    -> MetaSigma
        CharListSort
        (MetaVariable CharListSort)
        p1
        (MetaVariable CharListSort)
sigma2 phip = sigma2p phip psi1

sigma2p
    :: (MetaPattern CharListSort p1, MetaPattern CharListSort p2)
    => p1
    -> p2
    -> MetaSigma
        CharListSort
        p2
        p1
        p2
sigma2p phip psip = metaSigma phiSort psip phip psip

sigma3
    :: MetaPattern CharListSort p1
    => p1
    -> MetaSigma
        CharListSort
        (MetaVariable CharListSort)
        (MetaVariable CharListSort)
        p1
sigma3 = metaSigma phiSort psi1 psi1

data MetaSigmoid s p1 p2 p3 = MetaSigmoid
    { metaSigmoidSort   :: s
    , metaSigmoidFirst  :: p1
    , metaSigmoidSecond :: p2
    , metaSigmoidThird  :: p3
    }
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2, MetaPattern s p3)
    => ProperPattern Meta s (MetaSigmoid s p1 p2 p3)
  where
    asProperPattern (MetaSigmoid _ p1 p2 p3) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = sigmoidId
                , symbolOrAliasParams = []
                }
            , applicationChildren = [asAst p1, asAst p2, asAst p3]
            }
metaSigmoid
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2, MetaPattern s p3)
    => s -> p1 -> p2 -> p3 -> MetaSigmoid s p1 p2 p3
metaSigmoid = MetaSigmoid

sigmoid2
    :: MetaPattern CharListSort p1
    => p1
    -> MetaSigmoid
        CharListSort
        (MetaVariable CharListSort)
        p1
        (MetaVariable CharListSort)
sigmoid2 phip = sigmoid2p phip psi1

sigmoid2p
    :: (MetaPattern CharListSort p1, MetaPattern CharListSort p2)
    => p1
    -> p2
    -> MetaSigmoid
        CharListSort
        p2
        p1
        p2
sigmoid2p phip psip = metaSigmoid phiSort psip phip psip

sigmaId :: Id Meta
sigmaId = Id "#sigma"

sigmoidId :: Id Meta
sigmoidId = Id "#sigmoid"

sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sigmaId
    , symbolOrAliasParams = []
    }

sigmaSort :: CharListSort
sigmaSort = phiSort

sigmoidSymbol :: SymbolOrAlias Meta
sigmoidSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#sigmoid"
    , symbolOrAliasParams = []
    }

-- sigma(..., phi1 \/ phi2, ...)
--   -> (sigma(..., phi1, ...) \/ sigma(..., phi2, ...))
propagateOrTests :: TestTree
propagateOrTests =
    testGroup "Propagate Or tests"
        [ runTestScript "Fails if indexes do not match 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma3 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if indexes do not match 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma3 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if indexes do not match 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma3 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if indexes do not match 4"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    2
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi1 not matched 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort psi phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi1 not matched 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 psi)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi1 not matched 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    psi
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi2 not matched 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 psi))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 psi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi2 not matched 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 psi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if phi2 not matched 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    psi
                    (GoalId 1))
            ]
        , runTestScript "Fails if sigma not matched 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigmoid2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if sigma not matched 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigmoid2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if sigma not matched 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigmoid2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if sigma not matched 4"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmoidSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 1"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi (metaOr phiSort phi1 phi2) phi)
                    (metaOr phiSort
                        (metaSigma phiSort phi phi1 phi)
                        (metaSigma phiSort phi phi2 phi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 2"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaOr phiSort phi1 phi2) psi)
                    (metaOr phiSort
                        (metaSigma phiSort phi phi1 phi)
                        (metaSigma phiSort phi phi2 phi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 3"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaOr phiSort phi1 phi2) phi)
                    (metaOr phiSort
                        (metaSigma phiSort psi phi1 phi)
                        (metaSigma phiSort phi phi2 phi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 4"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaOr phiSort phi1 phi2) phi)
                    (metaOr phiSort
                        (metaSigma phiSort phi phi1 psi)
                        (metaSigma phiSort phi phi2 phi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 5"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaOr phiSort phi1 phi2) phi)
                    (metaOr phiSort
                        (metaSigma phiSort phi phi1 phi)
                        (metaSigma phiSort psi phi2 phi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Fails if extra patterns are different 6"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaOr phiSort phi1 phi2) phi)
                    (metaOr phiSort
                        (metaSigma phiSort phi phi1 phi)
                        (metaSigma phiSort phi phi2 psi)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateOr
                    sigmaSymbol
                    1
                    phi1
                    phi2
                    (GoalId 1))
            ]
        , runTestScript "Succeeds"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaOr phiSort phi1 phi2))
                    (metaOr phiSort
                        (sigma2 phi1)
                        (sigma2 phi2)
                    )
                )
                (NewGoalId 1)
            , testPropagateOr
                sigmaSymbol
                1
                phi1
                phi2
                (GoalId 1)
            ]
        ]

-- sigma(..., exists x . phi, ...) -> (exists x . sigma(..., phi1, ...))
-- where x does not occur free anywhere.
propagateExistsTests :: TestTree
propagateExistsTests =
    testGroup "Propagate Exists tests"
        [ runTestScript "Fails if indexes do not match 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma3 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if indexes do not match 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma3 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if indexes do not match 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    2
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if variables do not match 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort y phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if variables do not match 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort y (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if variables do not match 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    y
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if formulas do not match 1"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x psi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if formulas do not match 2"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 psi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Fails if formulas do not match 3"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    psi
                    (GoalId 1))
            ]
        , runTestScript "Fails if the additional patterns are different 1"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi (metaExists phiSort x phi) phi)
                    (metaExists phiSort x (metaSigma phiSort phi phi phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        , runTestScript "Fails if the additional patterns are different 2"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaExists phiSort x phi) psi)
                    (metaExists phiSort x (metaSigma phiSort phi phi phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        , runTestScript "Fails if variable is unquantified"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2p
                        (metaExists phiSort x phi) xEqualsX
                    )
                    (metaExists phiSort x
                        (sigma2p phi xEqualsX)
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        , runTestScript "Fails if the symbol is different 1"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigmoid phiSort phi (metaExists phiSort x phi) phi)
                    (metaExists phiSort x (metaSigma phiSort phi phi phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        , runTestScript "Fails if the symbol is different 2"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaExists phiSort x phi) phi)
                    (metaExists phiSort x (metaSigmoid phiSort phi phi phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmaSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        , runTestScript "Fails if the symbol is different 3"
            [ testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort phi (metaExists phiSort x phi) phi)
                    (metaExists phiSort x (metaSigma phiSort phi phi phi))
                )
                (NewGoalId 1)
            , expectFailure
                (testPropagateExists
                    sigmoidSymbol
                    1
                    x
                    phi
                    (GoalId 1))
            ]
        ,  runTestScript "Succeeds"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x phi))
                    (metaExists phiSort x (sigma2 phi))
                )
                (NewGoalId 1)
            , testPropagateExists
                sigmaSymbol
                1
                x
                phi
                (GoalId 1)
            ]
        , runTestScript "Succeeds when quantified"
            [ testAddGoal
                (metaImplies phiSort
                    (sigma2 (metaExists phiSort x xEqualsX))
                    (metaExists phiSort x (sigma2 xEqualsX))
                )
                (NewGoalId 1)
            , testPropagateExists
                sigmaSymbol
                1
                x
                xEqualsX
                (GoalId 1)
            ]
        ]

-- form phi->psi, deduce not sigma(..., phi, ...)->sigma(..., psi, ...))
framingTests :: TestTree
framingTests =
    testGroup "Framing tests"
        [ runTestScript "Fails if indexes do not match"
            [ testAddGoal (metaImplies phiSort phi psi) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi phi psi)
                    (metaSigma phiSort psi psi psi)
                )
                (NewGoalId 2)
            , expectFailure
                (testFraming
                    sigmaSymbol
                    2
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Fails if symbols do not match"
            [ testAddGoal (metaImplies phiSort phi psi) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigmoid phiSort psi phi psi)
                    (metaSigmoid phiSort psi psi psi)
                )
                (NewGoalId 2)
            , expectFailure
                (testFraming
                    sigmaSymbol
                    1
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Fails if hypothesis has wrong form"
            [ testAddGoal (metaNot phiSort phi) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi phi psi)
                    (metaSigma phiSort psi psi psi)
                )
                (NewGoalId 2)
            , expectFailure
                (testFraming
                    sigmaSymbol
                    1
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Fails if anteceedent formulas do not match"
            [ testAddGoal (metaImplies phiSort phi1 psi) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi phi psi)
                    (metaSigma phiSort psi psi psi)
                )
                (NewGoalId 2)
            , expectFailure
                (testFraming
                    sigmaSymbol
                    1
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Fails if consequent formulas do not match"
            [ testAddGoal (metaImplies phiSort phi psi1) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi phi psi)
                    (metaSigma phiSort psi psi psi)
                )
                (NewGoalId 2)
            , expectFailure
                (testFraming
                    sigmaSymbol
                    1
                    (GoalId 1)
                    (GoalId 2))
            ]
        , runTestScript "Succeeds"
            [ testAddGoal (metaImplies phiSort phi psi) (NewGoalId 1)
            , testAddGoal
                (metaImplies phiSort
                    (metaSigma phiSort psi phi psi)
                    (metaSigma phiSort psi psi psi)
                )
                (NewGoalId 2)
            , testFraming
                sigmaSymbol
                1
                (GoalId 1)
                (GoalId 2)
            ]
        ]

-- (exists x . x)
existenceTests :: TestTree
existenceTests =
    testGroup "Existence tests"
        [ runTestScript "Fails if the variable differs 1"
            [ testAddGoal
                (metaExists xSort y x)
                (NewGoalId 1)
            , expectFailure
                (testExistence
                    x
                    (GoalId 1))
            ]
        , runTestScript "Fails if the variable differs 2"
            [ testAddGoal
                (metaExists xSort x y)
                (NewGoalId 1)
            , expectFailure
                (testExistence
                    x
                    (GoalId 1))
            ]
        , runTestScript "Fails if the variable differs 3"
            [ testAddGoal
                (metaExists xSort x x)
                (NewGoalId 1)
            , expectFailure
                (testExistence
                    y
                    (GoalId 1))
            ]
        , runTestScript "Succeeds"
            [ testAddGoal
                (metaExists xSort x x)
                (NewGoalId 1)
            , testExistence
                x
                (GoalId 1)
            ]
        ]

-- (not ((C1 [x /\ phi]) /\ (C2 [x /\ (not phi)])))
singletonVariableTests :: TestTree
singletonVariableTests =
    testGroup "Singleton Variable tests"
        [ runTestScript "Fails if the variable differs 1"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi3 phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the variable differs 2"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi3 (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the variable differs 3"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi3
                    phi1
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the pattern differs 1"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi3)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the pattern differs 2"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi3))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the pattern differs 3"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi3
                    [1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 1"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    []
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 2"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    []
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 3"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1, 0]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 4"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [0, 0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 5"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [-1]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 6"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [0]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 7"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [2]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 8"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [3]
                    [0]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 9"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [-1]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 10"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [1]
                    (GoalId 1))
            ]
        , runTestScript "Fails if the path is broken 11"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , expectFailure
                (testSingvar
                    phi
                    phi1
                    [1]
                    [3]
                    (GoalId 1))
            ]
        , runTestScript "Succeeds"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaAnd phiSort phi phi1)
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , testSingvar
                phi
                phi1
                [1]
                [0]
                (GoalId 1)
            ]
        , runTestScript "Succeeds with long paths"
            [ testAddGoal
                (metaNot phiSort
                    (metaAnd phiSort
                        (metaSigma phiSort
                            phi2
                            (metaSigmoid phiSort
                                phi2
                                phi2
                                (metaAnd phiSort phi phi1)
                            )
                            phi2
                        )
                        (metaSigmoid phiSort
                            (metaAnd phiSort phi (metaNot phiSort phi1))
                            phi2
                            phi2
                        )
                    )
                )
                (NewGoalId 1)
            , testSingvar
                phi
                phi1
                [1, 2]
                [0]
                (GoalId 1)
            ]
        ]

-- TODO: Tests with failures to do things, e.g. using undefined IDs.

newtype NewGoalId = NewGoalId Int
newtype GoalId = GoalId Int
    deriving (Eq, Show, Ord)
instance Pretty GoalId where
    pretty (GoalId i) = pretty "goalId:" <> pretty i

type MLProof =
    Proof
        GoalId
        (MLRule
            (Sort Meta)
            (SymbolOrAlias Meta)
            (Variable Meta)
            (MetaMLPattern Variable)
        )
        (MetaMLPattern Variable)
data GoalMLProofState
    = GoalUnproven
    | GoalProven
    | GoalPartlyProven GoalNeeds
    deriving Show
newtype GoalNeeds = GoalNeeds [GoalId]
    deriving (Eq, Show)
emptyMLProof :: MLProof
emptyMLProof = emptyProof
goalCount :: MLProof -> Int
goalCount proof = length (claims proof)

stringError :: Either (Error MLError) a -> Either String a
stringError thing =
    case thing of
        Right a  -> Right a
        Left err -> Left (printError err)

addGoal
    :: UnifiedPattern -> NewGoalId -> MLProof -> Either String MLProof
addGoal formula (NewGoalId goalId) proof =
    stringError
        (HilbertProof.add
            (formulaVerifier defaultIndexedModule)
            proof
            (GoalId goalId)
            -- TODO(virgil) remove this patternKoreToMeta nonsense and generate
            -- MetaMLPatterns directly
            (patternKoreToMeta formula)
        )
modusPonens
    :: GoalId -> GoalId -> GoalId -> MLProof -> Either String MLProof
modusPonens phiId phiImpliesPsiId conclusionId proof =
    stringError modusPonens'
  where
    modusPonens' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (ModusPonens phiId phiImpliesPsiId)

proposition1
    :: UnifiedPattern
    -> UnifiedPattern
    -> GoalId
    -> MLProof
    -> Either String MLProof
proposition1 phip psip conclusionId proof =
    stringError proposition1'
  where
    proposition1' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Propositional1 (patternKoreToMeta phip) (patternKoreToMeta psip))

proposition2
    :: UnifiedPattern
    -> UnifiedPattern
    -> UnifiedPattern
    -> GoalId
    -> MLProof
    -> Either String MLProof
proposition2 phi1p phi2p phi3p conclusionId proof =
    stringError proposition2'
  where
    proposition2' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Propositional2
                (patternKoreToMeta phi1p)
                (patternKoreToMeta phi2p)
                (patternKoreToMeta phi3p)
            )

proposition3
    :: UnifiedPattern
    -> UnifiedPattern
    -> GoalId
    -> MLProof
    -> Either String MLProof
proposition3 phi1p phi2p conclusionId proof =
    stringError proposition3'
  where
    proposition3' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Propositional3 (patternKoreToMeta phi1p) (patternKoreToMeta phi2p))

variableSubstitution
    :: SubstitutingVariable (Variable Meta)
    -> SubstitutedVariable (Variable Meta)
    -> UnifiedPattern
    -> GoalId
    -> MLProof
    -> Either String MLProof
variableSubstitution
    substituting substituted unsubstitutedPattern conclusionId proof
  =
    stringError variableSubstitution'
  where
    variableSubstitution' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (VariableSubstitution
                substituted
                (patternKoreToMeta unsubstitutedPattern)
                substituting
            )

forallRule
    :: Variable Meta
    -> UnifiedPattern
    -> UnifiedPattern
    -> GoalId
    -> MLProof
    -> Either String MLProof
forallRule
    variable phi1p phi2p conclusionId proof
  =
    stringError forallFormula'
  where
    forallFormula' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (ForallRule
                variable (patternKoreToMeta phi1p) (patternKoreToMeta phi2p)
            )

generalization
    :: Variable Meta -> GoalId -> GoalId -> MLProof -> Either String MLProof
generalization variable phiId conclusionId proof =
    stringError generalization'
  where
    generalization' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Generalization variable phiId)

propagateOr
    :: SymbolOrAlias Meta
    -> Int
    -> UnifiedPattern
    -> UnifiedPattern
    -> GoalId
    -> MLProof -> Either String MLProof
propagateOr symbol idx phi1p phi2p conclusionId proof =
    stringError propagateOr'
  where
    propagateOr' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (PropagateOr
                symbol idx (patternKoreToMeta phi1p) (patternKoreToMeta phi2p)
            )

propagateExists
    :: SymbolOrAlias Meta
    -> Int
    -> Variable Meta
    -> UnifiedPattern
    -> GoalId
    -> MLProof -> Either String MLProof
propagateExists symbol idx variable phip conclusionId proof =
    stringError propagateOr'
  where
    propagateOr' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (PropagateExists symbol idx variable (patternKoreToMeta phip))

framing
    :: SymbolOrAlias Meta
    -> Int
    -> GoalId
    -> GoalId
    -> MLProof -> Either String MLProof
framing symbol idx hypothesisId conclusionId proof =
    stringError propagateFraming'
  where
    propagateFraming' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Framing symbol idx hypothesisId)

existence
    :: Variable Meta
    -> GoalId
    -> MLProof -> Either String MLProof
existence variable conclusionId proof =
    stringError existence'
  where
    existence' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Existence variable)

singvar
    :: Variable Meta
    -> UnifiedPattern
    -> [Int]
    -> [Int]
    -> GoalId
    -> MLProof -> Either String MLProof
singvar variable phip path1 path2 conclusionId proof =
    stringError singvar'
  where
    singvar' = do
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Singvar variable (patternKoreToMeta phip) path1 path2)

-- Inefficient implementation, but good enough for tests.
goalState :: GoalId -> MLProof -> Maybe GoalMLProofState
goalState goalId proof =
    case Map.lookup goalId (index proof) of
        Nothing -> Nothing
        _ ->
            case Map.lookup goalId (derivations proof) of
                Nothing -> Just GoalUnproven
                Just rule ->
                    snd
                        (foldl'
                            combineStates
                            (goalId, Just GoalProven)
                            (fmap
                                goalStateAndIndex
                                rule
                            )
                        )
  where
    goalStateAndIndex idx = (idx, goalState idx proof)
    combineStates (idx, Nothing) _ =
        (idx, Nothing)
    combineStates (idx, _) (_, Nothing) =
        (idx, Nothing)
    combineStates state (_, Just GoalProven) = state
    combineStates (idx, Just GoalProven) (childIdx, _) =
        (idx, Just (GoalPartlyProven (GoalNeeds [childIdx])))
    combineStates
        (idx, Just (GoalPartlyProven (GoalNeeds idxs)))
        (childIdx, _)
      =
        (idx, Just (GoalPartlyProven (GoalNeeds (childIdx:idxs))))

lookupGoal :: GoalId -> MLProof -> Maybe (MetaMLPattern Variable)
lookupGoal goalId proof = snd <$> Map.lookup goalId (index proof)

lookupFormula
    :: GoalId
    -> MLProof
    -> Either (Error MLError) (MetaMLPattern Variable)
lookupFormula goalId proof =
    case Map.lookup goalId (index proof) of
        Nothing ->
            koreFail ("Formula with ID '" ++ show goalId ++ "' not found.")
        Just (_, formula) -> return formula

testAddGoal
    :: AsAst UnifiedPattern p
    => p
    -> NewGoalId
    -> (String, MLProof -> Either String MLProof)
testAddGoal pattern1 (NewGoalId goalId) =
    ( "adding " ++ show unifiedPattern ++ " with ID=" ++ show goalId
    , addGoal unifiedPattern (NewGoalId goalId)
    )
  where
    unifiedPattern = asAst pattern1

testModusPonens
    :: GoalId
    -> GoalId
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testModusPonens implierId implicationId impliedId =
    ( "modus ponens with phi=" ++ show implierId
        ++ " phi->psi=" ++ show implicationId
        ++ " and psi=" ++ show impliedId
    , modusPonens implierId implicationId impliedId
    )

testProposition1
    :: (AsAst UnifiedPattern p1, AsAst UnifiedPattern p2)
    => p1
    -> p2
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testProposition1 phip psip conclusion =
    ( "proposition 1 with phi="
        ++ show patPhi
        ++ " psi="
        ++ show patPsi
        ++ " conclusion="
        ++ show conclusion
    , proposition1 patPhi patPsi conclusion
    )
  where
    patPhi = asAst phip
    patPsi = asAst psip

testProposition2
    ::  ( AsAst UnifiedPattern p1
        , AsAst UnifiedPattern p2
        , AsAst UnifiedPattern p3
        )
    => p1
    -> p2
    -> p3
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testProposition2 phi1p phi2p phi3p conclusion =
    ( "proposition 2 with phi1=" ++ show pat1
        ++ " phi2=" ++ show pat2
        ++ " phi3=" ++ show pat3
        ++ " conclusion=" ++ show conclusion
    , proposition2 pat1 pat2 pat3 conclusion
    )
  where
    pat1 = asAst phi1p
    pat2 = asAst phi2p
    pat3 = asAst phi3p

testProposition3
    :: (AsAst UnifiedPattern p1, AsAst UnifiedPattern p2)
    => p1
    -> p2
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testProposition3 phi1p phi2p conclusion =
    ( "proposition 3 with phi1=" ++ show pat1
        ++ " phi2=" ++ show pat2
        ++ " conclusion=" ++ show conclusion
    , proposition3 pat1 pat2 conclusion
    )
  where
    pat1 = asAst phi1p
    pat2 = asAst phi2p

testVariableSubstitution
    :: AsAst UnifiedPattern p1
    => SubstitutingVariable (Variable Meta)
    -> SubstitutedVariable (Variable Meta)
    -> p1
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testVariableSubstitution
    substituting substituted unsubstitutedPattern conclusion
  =
    ( "variable substitution with y=" ++ show substituting
        ++ " and x=" ++ show substituted
        ++ " and phi(x)=" ++ show phip
    , variableSubstitution substituting substituted phip conclusion
    )
  where
    phip = asAst unsubstitutedPattern

testForall
    :: (MetaSort s, AsAst UnifiedPattern p1, AsAst UnifiedPattern p2)
    => MetaVariable s
    -> p1
    -> p2
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testForall
    variable phi1p phi2p conclusion
  =
    ( "forall with x=" ++ show var1
        ++ " and phi1=" ++ show pat1
        ++ " and phi2(x)=" ++ show pat2
    , forallRule var1 pat1 pat2 conclusion
    )
  where
    var1 = asMetaVariable variable
    pat1 = asAst phi1p
    pat2 = asAst phi2p

testGeneralization
    :: MetaSort s
    => MetaVariable s
    -> GoalId
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testGeneralization variable phiId conclusionId =
    ( "generalization with x=" ++ show var
        ++ " phi=" ++ show phiId
    , generalization var phiId conclusionId
    )
  where
    var = asMetaVariable variable

testPropagateOr
    :: (AsAst UnifiedPattern p1, AsAst UnifiedPattern p2)
    => SymbolOrAlias Meta
    -> Int
    -> p1
    -> p2
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testPropagateOr symbol idx phi1p phi2p conclusionId =
    ( "propagate or with sigma=" ++ show symbol
        ++ " idx=" ++ show idx
        ++ " phi1=" ++ show pat1
        ++ " phi2=" ++ show pat2
    , propagateOr symbol idx pat1 pat2 conclusionId
    )
  where
    pat1 = asAst phi1p
    pat2 = asAst phi2p

testPropagateExists
    :: (MetaSort s, AsAst UnifiedPattern p1)
    => SymbolOrAlias Meta
    -> Int
    -> MetaVariable s
    -> p1
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testPropagateExists symbol idx variable phip conclusionId =
    ( "propagate exists with sigma=" ++ show symbol
        ++ " idx=" ++ show idx
        ++ " x=" ++ show var
        ++ " phi=" ++ show pat
    , propagateExists symbol idx var pat conclusionId
    )
  where
    pat = asAst phip
    var = asMetaVariable variable

testFraming
    :: SymbolOrAlias Meta
    -> Int
    -> GoalId
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testFraming symbol idx hypothesisId conclusionId =
    ( "framing with sigma=" ++ show symbol
        ++ " idx=" ++ show idx
        ++ " hypothesis=" ++ show hypothesisId
    , framing symbol idx hypothesisId conclusionId
    )

testExistence
    :: MetaSort s
    => MetaVariable s
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testExistence variable conclusionId =
    ( "existence with var=" ++ show var
    , existence var conclusionId
    )
  where
    var = asMetaVariable variable

testSingvar
    :: (MetaSort s, AsAst UnifiedPattern p1)
    => MetaVariable s
    -> p1
    -> [Int]
    -> [Int]
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testSingvar variable phip path1 path2 conclusionId =
    ( "singvar"
        ++ " with var=" ++ show var
        ++ " phi=" ++ show pat
        ++ " path1=" ++ show path1
        ++ " path2=" ++ show path2
    , singvar var pat path1 path2 conclusionId
    )
  where
    var = asMetaVariable variable
    pat = asAst phip

assertGoalCount :: Int -> (String, MLProof -> Either String MLProof)
assertGoalCount count =
    ( "expecting the goal count to be " ++ show count
    , goalCountAssertion count
    )
goalCountAssertion :: Int -> (MLProof -> Either String MLProof)
goalCountAssertion count proof =
    if count == actualGoalCount
        then Right proof
        else Left ("actual goal count is " ++ show actualGoalCount)
  where
    actualGoalCount = goalCount proof

assertGoal
    :: AsAst UnifiedPattern p
    => GoalId
    -> p
    -> (String, MLProof -> Either String MLProof)
assertGoal goalId pattern1 =
    ( "expecting the goal to be " ++ show unifiedPattern
    , goalAssertion goalId unifiedPattern
    )
  where
    unifiedPattern = asAst pattern1
goalAssertion
    :: GoalId
    -> UnifiedPattern
    -> (MLProof -> Either String MLProof)
goalAssertion goalId pattern1 proof =
    case lookupGoal goalId proof of
        Nothing -> Left ("Goal with id " ++ show goalId ++ " not found.")
        Just actualPattern ->
            if actualPattern /= patternKoreToMeta pattern1
                then Left ("the actual goal is" ++ show actualPattern)
                else Right proof

assertUnproven :: GoalId -> (String, MLProof -> Either String MLProof)
assertUnproven (GoalId goalId) =
    ( "expecting the goal with id #" ++ show goalId ++ " to be unproven"
    , unprovenAssertion (GoalId goalId)
    )
unprovenAssertion :: GoalId -> (MLProof -> Either String MLProof)
unprovenAssertion goalId proof =
    case goalState goalId proof of
        Just GoalUnproven -> Right proof
        state             -> Left ("the goal is " ++ show state)

assertPartlyProven
    :: GoalId
    -> GoalNeeds
    -> (String, MLProof -> Either String MLProof)
assertPartlyProven (GoalId goalId) expectedDependencies =
    ( "expecting the goal with id #" ++ show goalId ++ " to be partly proven"
    , partlyProvenAssertion (GoalId goalId) expectedDependencies
    )
partlyProvenAssertion
    :: GoalId
    -> GoalNeeds
    -> (MLProof -> Either String MLProof)
partlyProvenAssertion goalId expectedDependencies proof =
    case goalState goalId proof of
        Just (GoalPartlyProven actualDependencies) ->
            if actualDependencies /= expectedDependencies
                then
                    Left
                        (  "different unproven dependencies, expected="
                        ++ show expectedDependencies
                        ++ " actual="
                        ++ show actualDependencies)
                else Right proof
        state -> Left ("the goal is " ++ show state)

assertProven :: GoalId -> (String, MLProof -> Either String MLProof)
assertProven (GoalId goalId) =
    ( "expecting the goal with id #" ++ show goalId ++ " to be proven"
    , provenAssertion (GoalId goalId)
    )
provenAssertion :: GoalId -> (MLProof -> Either String MLProof)
provenAssertion goalId proof =
    case goalState goalId proof of
        Just GoalProven -> Right proof
        state           -> Left ("the goal is " ++ show state)

runTestScript
    :: String
    -> [(String, MLProof -> Either String MLProof)]
    -> TestTree
runTestScript description actions =
    testCase description
        (case foldM runAction emptyMLProof actionsWithDescriptions of
            Left err -> assertFailure err
            Right _  -> return ()
        )
  where
    actionName idx (description1, action) =
        ("Action #" ++ show idx ++ " (" ++ description1 ++ ")", action)
    actionsWithDescriptions = zipWith actionName [(0::Int)..] actions

expectFailure
    :: (String, MLProof -> Either String MLProof)
    -> (String, MLProof -> Either String MLProof)
expectFailure (actionDescription, action) =
    ( "expecting failure for action: "
        ++ actionDescription ++ "'"
    , failureExpected action
    )
failureExpected
    :: (MLProof -> Either String MLProof)
    -> MLProof
    -> Either String MLProof
failureExpected action proof =
    case action proof of
        Right _ -> Left "action did not complete with error"
        Left _  -> Right proof

runAction
    :: MLProof
    -> (String, MLProof -> Either String MLProof)
    -> Either String MLProof
runAction proof (description, action) =
    case action proof of
        Left err -> Left (description ++ " : " ++ err)
        result   -> result

defaultIndexedModule :: KoreIndexedModule
defaultIndexedModule =
    case defaultIndexedModuleWithError of
        Left err -> error (printError err)
        Right m  -> m

defaultIndexedModuleWithError :: Either (Error MLError) KoreIndexedModule
defaultIndexedModuleWithError = do
    modules <-
        castError (verifyAndIndexDefinition DoNotVerifyAttributes definition)
    case Map.lookup moduleName1 modules of
        Just a -> return a
        Nothing ->
            koreFail "Internal error: the implicit kore module was not indexed."
  where
    moduleName1 = ModuleName "test-module"
    definition = Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Module
                { moduleName = moduleName1
                , moduleSentences =
                    [ MetaSentence
                        ( SentenceSymbolSentence SentenceSymbol
                            { sentenceSymbolSymbol = Symbol
                                { symbolConstructor = sigmaId
                                , symbolParams = []
                                }
                            , sentenceSymbolSorts =
                                [ asAst sigmaSort
                                , asAst sigmaSort
                                , asAst sigmaSort
                                ]
                            , sentenceSymbolResultSort = asAst sigmaSort
                            , sentenceSymbolAttributes = Attributes []
                            }
                        )
                    , MetaSentence
                        ( SentenceSymbolSentence SentenceSymbol
                            { sentenceSymbolSymbol = Symbol
                                { symbolConstructor = sigmoidId
                                , symbolParams = []
                                }
                            , sentenceSymbolSorts =
                                [ asAst sigmaSort
                                , asAst sigmaSort
                                , asAst sigmaSort
                                ]
                            , sentenceSymbolResultSort = asAst sigmaSort
                            , sentenceSymbolAttributes = Attributes []
                            }
                        )
                    ]
                , moduleAttributes = Attributes []
                }
            ]
        }
