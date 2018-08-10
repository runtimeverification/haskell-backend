{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Description: Matching logic rules for Kore patterns
-}
module Logic.Matching.Rules.Kore where

import           Data.Functor.Foldable
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( And (..), Application (..), Exists (..), Implies (..),
                 Not (..), Or (..), Pattern (..), SymbolOrAlias (..),
                 Variable )
import qualified Kore.AST.Common as Common
                 ( Forall (..) )
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Meta (..), Unified (..) )
import           Kore.AST.PureToKore
                 ( patternPureToKore )
import           Kore.ASTVerifier.PatternVerifier
                 ( verifyPattern )
import           Kore.Error
                 ( Error, castError, koreFail, koreFailWhen, withContext )
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.MetaML.AST
                 ( CommonMetaPattern, metaFreeVariables )
import           Kore.Substitution.Class
                 ( PatternSubstitutionClass (..) )
import qualified Kore.Substitution.List as Substitution
import           Kore.Unparser.Unparse
                 ( Unparse, unparseToString )
import           Kore.Variables.Fresh.Class
                 ( FreshVariablesClass (..) )
import           Kore.Variables.Sort
                 ( TermWithSortVariablesClass (sortVariables) )
import           Logic.Matching.Error
                 ( MLError )
import           Logic.Matching.Rules.Minimal
                 ( MLRule (..), SubstitutedVariable (..),
                 SubstitutingVariable (..) )
import           Logic.Proof.Hilbert
                 ( ProofSystem (..) )

type Var = Variable Meta
type Symbol = SymbolOrAlias Meta
type Formula = CommonMetaPattern
type Rule = MLRule Symbol Var Formula


-- To get an indexed module one can use `verifyAndIndexDefinition`
formulaVerifier
    :: KoreIndexedModule atts
    -> CommonMetaPattern
    -> Either (Error MLError) ()
formulaVerifier indexedModule formula = do
    castError
        (verifyPattern
            unifiedFormula
            Nothing
            indexedModule
            (sortVariables unifiedFormula)
        )
    return ()
  where
    unifiedFormula = patternPureToKore formula

-- TODO(virgil): Check that symbols and not aliases are used in a few places
-- like checkSingvar
instance ProofSystem
        MLError
        (MLRule
            (SymbolOrAlias Meta)
            (Variable Meta)
            CommonMetaPattern)
        CommonMetaPattern
  where
    checkDerivation conclusion (Propositional1 phi psi) =
        checkPropositional1Derivation phi psi conclusion
    checkDerivation conclusion (Propositional2 phi1 phi2 phi3) =
        checkPropositional2Derivation phi1 phi2 phi3 conclusion
    checkDerivation conclusion (Propositional3 phi1 phi2) =
        checkPropositional3Derivation phi1 phi2 conclusion
    checkDerivation conclusion (ModusPonens phi phiImpliesPsi) =
        checkModusPonensDerivation phi phiImpliesPsi conclusion
    checkDerivation conclusion (Generalization variable phi) =
        checkGeneralizationDerivation variable phi conclusion
    checkDerivation
        conclusion (VariableSubstitution substituted phi substituting)
      =
        checkVariableSubstitution substituting substituted phi conclusion
    checkDerivation conclusion (ForallRule variable phi1 phi2) =
        checkForall variable phi1 phi2 conclusion
    checkDerivation conclusion (PropagateOr symbol idx phi1 phi2) =
        checkPropagateOr symbol idx phi1 phi2 conclusion
    checkDerivation conclusion (PropagateExists symbol idx variable phi) =
        checkPropagateExists symbol idx variable phi conclusion
    checkDerivation conclusion (Framing symbol idx phi) =
        checkFraming symbol idx phi conclusion
    checkDerivation conclusion (Existence variable) =
        checkExistence variable conclusion
    checkDerivation conclusion (Singvar variable phi path1 path2) =
        checkSingvar variable phi path1 path2 conclusion

checkPropositional1Derivation
    :: CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkPropositional1Derivation phi psi topImplication
  = do
    (phi1, phi2, phi3) <-
        case topImplication of
            Fix
                (ImpliesPattern Implies
                    { impliesFirst = a
                    , impliesSecond = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst = b
                            , impliesSecond = c
                            }
                        )
                    }
                )
                -> return (a, b, c)
            _ -> koreFail
                "Expected a pattern of the form (phi1 -> (phi2 -> phi3))."
    testFormulaEquality
        phi1 "phi1 in (phi1 -> (phi2 -> phi3))"
        phi "phi in (Propositional1 phi psi)"
    testFormulaEquality
        phi2 "phi2 in (phi1 -> (phi2 -> phi3))"
        psi "psi in (Propositional1 phi psi)"
    testFormulaEquality
        phi3 "phi3 in (phi1 -> (phi2 -> phi3))"
        phi "phi in (Propositional1 phi psi)"

checkPropositional2Derivation
    :: CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkPropositional2Derivation phi1 phi2 phi3 conclusion
  = do
    (psi1, psi2, psi3, psi4, psi5, psi6, psi7) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst = a
                            , impliesSecond = Fix
                                ( ImpliesPattern Implies
                                    { impliesFirst = b
                                    , impliesSecond = c
                                    }
                                )
                            }
                        )
                    , impliesSecond = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst = Fix
                                ( ImpliesPattern Implies
                                    { impliesFirst = d
                                    , impliesSecond = e
                                    }
                                )
                            , impliesSecond = Fix
                                ( ImpliesPattern Implies
                                    { impliesFirst = f
                                    , impliesSecond = g
                                    }
                                )
                            }
                        )
                    }
                )
                -> return (a, b, c, d, e, f, g)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        psi1 (nameInKind "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi2 (nameInKind "psi2")
        phi2 (nameInProposition "phi2")
    testFormulaEquality
        psi3 (nameInKind "psi3")
        phi3 (nameInProposition "phi3")
    testFormulaEquality
        psi4 (nameInKind "psi4")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi5 (nameInKind "psi5")
        phi2 (nameInProposition "phi2")
    testFormulaEquality
        psi6 (nameInKind "psi6")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi7 (nameInKind "psi7")
        phi3 (nameInProposition "phi3")
  where
    kind = "((psi1 -> (psi2 -> psi3)) -> ((psi4 -> psi5) -> (psi6 -> psi7)))"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name = name ++ " in Propositional2(phi1, phi2, phi3)"

checkPropositional3Derivation
    :: CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkPropositional3Derivation phi1 phi2 conclusion
  = do
    (psi1, psi2, psi3, psi4) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst =
                                Fix (NotPattern Not { notChild = a })
                            , impliesSecond =
                                Fix (NotPattern Not { notChild = b })
                            }
                        )
                    , impliesSecond = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst = c
                            , impliesSecond = d
                            }
                        )
                    }
                )
                -> return (a, b, c, d)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        psi1 (nameInKind "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi2 (nameInKind "psi2")
        phi2 (nameInProposition "phi2")
    testFormulaEquality
        psi3 (nameInKind "psi3")
        phi2 (nameInProposition "phi1")
    testFormulaEquality
        psi4 (nameInKind "psi4")
        phi1 (nameInProposition "phi1")
  where
    kind = "((not psi1 -> not psi2) -> (psi3 -> psi4))"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name = name ++ " in Propositional3(phi1, phi2)"

checkModusPonensDerivation
    :: CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkModusPonensDerivation phi1 psi1ImpliesPsi2 conclusion
  = do
    (psi1, psi2) <-
        case psi1ImpliesPsi2 of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = a
                    , impliesSecond = b
                    }
                )
                -> return (a, b)
            _ -> koreFail
                    (  "Expected "
                    ++ nameInProposition "psi2"
                    ++ "a meta-pattern of the form "
                    ++ kind
                    ++ "."
                    )
    testFormulaEquality
        psi1 (nameInKind "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi2 (nameInKind "psi2")
        conclusion (nameInProposition "phi3")
  where
    kind = "phi2=(psi1 -> psi2)"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name = name ++ " in ModusPonens(phi1, phi2, phi3)"

instance FreshVariablesClass (Either (Error MLError)) Variable where
    freshVariable _ = koreFail "Did not expect variable capturing"
    freshVariableSuchThat v _ = freshVariable v

type MetaPatternSubstitution =
    Substitution.Substitution (Unified Variable) CommonKorePattern

instance
    PatternSubstitutionClass
        Substitution.Substitution
        Variable
        (Pattern Meta)
        (Either (Error MLError))
  where

checkVariableSubstitution
    :: SubstitutingVariable (Variable Meta)
    -> SubstitutedVariable (Variable Meta)
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkVariableSubstitution
    (SubstitutingVariable substituting)
    (SubstitutedVariable substituted)
    beforeSubstitution
    conclusion
  = do
    (var, psi1, psi2) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = Fix
                        ( ForallPattern Common.Forall
                            { Common.forallVariable = v1
                            , Common.forallChild = p1
                            }
                        )
                    , impliesSecond = p2
                    }
                )
                -> return (v1, p1, p2)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        var (nameInKind "x")
        substituted (nameInProposition "substituted")
    testFormulaEquality
        psi1 (nameInKind "psi1")
        beforeSubstitution (nameInProposition "phi")
    afterSubstitution <-
        substitute
            beforeSubstitution
            (Substitution.fromList
                [   ( UnifiedMeta substituted
                    , substitutingPattern
                    )
                ]
            )
    testFormulaEquality
        psi2 (nameInKind "psi2")
        afterSubstitution (nameInProposition "phi[substituting/substituted]")
  where
    kind = "((forall x . psi1) -> psi2)"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name =
        name ++ " in VariableSubstitution(substituting, substituted, phi)"
    substitutingPattern = Fix (VariablePattern substituting)

checkForall
    :: Variable Meta
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkForall variable phi1 phi2 conclusion
  = do
    (var1, var2, psi1, psi2, psi3, psi4) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = Fix
                        ( ForallPattern Common.Forall
                            { Common.forallVariable = v1
                            , Common.forallChild = Fix
                                ( ImpliesPattern Implies
                                    { impliesFirst = p1
                                    , impliesSecond = p2
                                    }
                                )
                            }
                        )
                    , impliesSecond = Fix
                        ( ImpliesPattern Implies
                            { impliesFirst = p3
                            , impliesSecond = Fix
                                ( ForallPattern Common.Forall
                                    { Common.forallVariable = v2
                                    , Common.forallChild = p4
                                    }
                                )
                            }
                        )
                    }
                )
                -> return (v1, v2, p1, p2, p3, p4)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        var1 (nameInKind "x")
        variable (nameInProposition "v")
    testFormulaEquality
        var2 (nameInKind "y")
        variable (nameInProposition "v")
    testFormulaEquality
        psi1 (nameInKind "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi3 (nameInKind "psi3")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi2 (nameInKind "psi2")
        phi2 (nameInProposition "phi2")
    testFormulaEquality
        psi4 (nameInKind "psi4")
        phi2 (nameInProposition "phi2")
    let freeVars = metaFreeVariables phi1
    koreFailWhen (variable `Set.member` freeVars)
        "v should not occur free in phi1 in Forall(v, phi1, phi3)"
    return ()
  where
    kind = "((forall x . (psi1 -> psi2)) -> (psi3 -> forall y . psi4))"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name = name ++ " in Forall(v, phi1, phi3)"

checkGeneralizationDerivation
    :: Variable Meta
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkGeneralizationDerivation variable phi conclusion
  = do
    (var, psi) <-
        case conclusion of
            Fix
                ( ForallPattern Common.Forall
                    { Common.forallVariable = a
                    , Common.forallChild = b
                    }
                )
                -> return (a, b)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        var (nameInKind "x")
        variable (nameInProposition "v")
    testFormulaEquality
        psi (nameInKind "psi")
        phi (nameInProposition "phi")
  where
    kind = "(forall x . psi)"
    nameInKind name = name ++ " in " ++ kind
    nameInProposition name = name ++ " in Generalization(v, phi)"

checkPropagateOr
    :: SymbolOrAlias Meta
    -> Int
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkPropagateOr symbol idx phi1 phi2 conclusion
  = do
    (sym1, sym2, sym3, patterns1, patterns2, patterns3) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = Fix
                        ( ApplicationPattern Application
                            { applicationSymbolOrAlias = s1
                            , applicationChildren = c1
                            }
                        )
                    , impliesSecond = Fix
                        ( OrPattern Or
                            { orFirst = Fix
                                ( ApplicationPattern Application
                                    { applicationSymbolOrAlias = s2
                                    , applicationChildren = c2
                                    }
                                )
                            , orSecond = Fix
                                ( ApplicationPattern Application
                                    { applicationSymbolOrAlias = s3
                                    , applicationChildren = c3
                                    }
                                )
                            }
                        )
                    }
                )
                -> return (s1, s2, s3, c1, c2, c3)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind0 ++ ".")
    testFormulaEquality
        sym1 (nameInKind0 "#sigma1{...}")
        symbol (nameInProposition "symbol")
    testFormulaEquality
        sym2 (nameInKind0 "#sigma2{...}")
        symbol (nameInProposition "symbol")
    testFormulaEquality
        sym3 (nameInKind0 "#sigma3{...}")
        symbol (nameInProposition "symbol")
    koreFailWhen (length patterns2 /= length patterns1)
        ("Inconsistent argument list size for " ++ nameInProposition "sigma")
    koreFailWhen (length patterns3 /= length patterns1)
        ("Inconsistent argument list size for " ++ nameInProposition "sigma")
    koreFailWhen (idx < 0)
        (nameInProposition "idx" ++ " must not be negative.")
    koreFailWhen (idx >= length patterns1)
        (  nameInProposition "idx"
        ++ " must be lower than the argument count for symbol ("
        ++ show (length patterns1)
        ++ ")."
        )
    let disjunction = patterns1 !! idx
    (psi1, psi2) <-
        case disjunction of
            Fix
                ( OrPattern Or
                    { orFirst = a
                    , orSecond = b
                    }
                )
                -> return (a, b)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind2 ++ ".")
    testFormulaEquality
        psi1 (nameInKind2 "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        psi2 (nameInKind2 "psi2")
        phi2 (nameInProposition "phi2")
    testFormulaEquality
        (patterns2 !! idx) (nameInKind3 "psi1")
        phi1 (nameInProposition "phi1")
    testFormulaEquality
        (patterns3 !! idx) (nameInKind4 "psi2")
        phi2 (nameInProposition "phi2")
    withContext
        (  "comparing the pattern lists for #sigma1{...} and #sigma2{...} in "
        ++ kind0
        )
        (testExtraPatternsEquality patterns1 patterns2 idx 0)
    withContext
        (  "comparing the pattern lists for #sigma1{...} and #sigma3{...} in "
        ++ kind0
        )
        (testExtraPatternsEquality patterns1 patterns3 idx 0)
  where
    kind0 = "(#sigma1{...}(...) -> (#sigma2{...}(...) \\/ #sigma3{...}(...)))"
    kind2 =
        "(#sigma1{...}(... psi1 \\/ psi2 ...) ->"
        ++ " (#sigma2{...}(...) \\/ #sigma3{...}(...)))"
    kind3 =
        "(#sigma1{...}(...) ->"
        ++ " (#sigma2{...}(... psi1 ...) \\/ #sigma3{...}(...)))"
    kind4 =
        "(#sigma1{...}(...) ->"
        ++ " (#sigma2{...}(...) \\/ #sigma3{...}(... psi2 ...)))"
    nameInKind0 name = name ++ " in " ++ kind0
    nameInKind2 name = name ++ " in " ++ kind2
    nameInKind3 name = name ++ " in " ++ kind3
    nameInKind4 name = name ++ " in " ++ kind4
    nameInProposition name = name ++ " in PropagateOr(symbol, idx, phi1, phi2)"

checkPropagateExists
    :: SymbolOrAlias Meta
    -> Int
    -> Variable Meta
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkPropagateExists symbol idx variable phi conclusion
  = do
    (application, var1, sym1, sym2, patterns1, patterns2) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst =
                        a@(Fix
                            ( ApplicationPattern Application
                                { applicationSymbolOrAlias = s1
                                , applicationChildren = c1
                                }
                            )
                        )
                    , impliesSecond = Fix
                        ( ExistsPattern Exists
                            { existsVariable = v
                            , existsChild = Fix
                                ( ApplicationPattern Application
                                    { applicationSymbolOrAlias = s2
                                    , applicationChildren = c2
                                    }
                                )
                            }
                        )
                    }
                )
                -> return (a, v, s1, s2, c1, c2)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind1 ++ ".")
    testFormulaEquality
        sym1 (nameInKind1 "#sigma1{...}")
        symbol (nameInProposition "symbol")
    testFormulaEquality
        sym2 (nameInKind1 "#sigma2{...}")
        symbol (nameInProposition "symbol")
    testFormulaEquality
        var1 (nameInKind1 "x")
        variable (nameInProposition "v")
    koreFailWhen (length patterns2 /= length patterns1)
        ("Inconsistent argument list size for " ++ nameInProposition "sigma")
    koreFailWhen (idx < 0)
        (nameInProposition "idx" ++ " must not be negative.")
    koreFailWhen (idx >= length patterns1)
        (  nameInProposition "idx"
        ++ " must be lower than the argument count for symbol ("
        ++ show (length patterns1)
        ++ ")."
        )
    let freeVars = metaFreeVariables application
    koreFailWhen (variable `Set.member` freeVars)
        (  "v should not occur free in ("
        ++ nameInKind1 "sigma1{...}(...)"
        ++ ")"
        )
    let quantification = patterns1 !! idx
    (var2, psi1) <-
        case quantification of
            Fix
                ( ExistsPattern Exists
                    { existsVariable = a
                    , existsChild = b
                    }
                )
                -> return (a, b)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind2 ++ ".")
    testFormulaEquality
        psi1 (nameInKind2 "psi")
        phi (nameInProposition "phi")
    testFormulaEquality
        var2 (nameInKind2 "y")
        variable (nameInProposition "v")

    testFormulaEquality
        (patterns2 !! idx) (nameInKind3 "psi")
        phi (nameInProposition "phi")

    withContext
        (  "comparing the pattern lists for #sigma1{...} and #sigma2{...} in "
        ++ kind1
        )
        (testExtraPatternsEquality patterns1 patterns2 idx 0)
    -- TODO: test the other term equality
  where
    kind1 = "(#sigma1{...}(...) -> (exists x . #sigma2{...}(...)))"
    kind2 =
        "(#sigma1{...}(... exists y . psi ...) ->"
        ++ " (exists x . #sigma2{...}(...)))"
    kind3 =
        "(#sigma1{...}(...) ->"
        ++ " (exists x . #sigma2{...}(... psi ...)))"
    nameInKind1 name = name ++ " in " ++ kind1
    nameInKind2 name = name ++ " in " ++ kind2
    nameInKind3 name = name ++ " in " ++ kind3
    nameInProposition name =
        name ++ " in PropagateExists(symbol, idx, v, phi)"

checkFraming
    :: SymbolOrAlias Meta
    -> Int
    -> CommonMetaPattern
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkFraming symbol idx hypothesis conclusion
  = do
    (sym1, sym2, patterns1, patterns2) <-
        case conclusion of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst =
                        (Fix
                            ( ApplicationPattern Application
                                { applicationSymbolOrAlias = s1
                                , applicationChildren = c1
                                }
                            )
                        )
                    , impliesSecond =
                        (Fix
                            ( ApplicationPattern Application
                                { applicationSymbolOrAlias = s2
                                , applicationChildren = c2
                                }
                            )
                        )
                    }
                )
                -> return (s1, s2, c1, c2)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind1 ++ ".")
    testFormulaEquality
        sym1 (nameInKind1 "#sigma1{...}")
        symbol (nameInProposition "symbol")
    testFormulaEquality
        sym2 (nameInKind1 "#sigma2{...}")
        symbol (nameInProposition "symbol")
    koreFailWhen (length patterns2 /= length patterns1)
        ("Inconsistent argument list size for " ++ nameInProposition "sigma")
    koreFailWhen (idx < 0)
        (nameInProposition "idx" ++ " must not be negative.")
    koreFailWhen (idx >= length patterns1)
        (  nameInProposition "idx"
        ++ " must be lower than the argument count for symbol ("
        ++ show (length patterns1)
        ++ ")."
        )
    let patA = patterns1 !! idx
    let patB = patterns2 !! idx
    (hypA,hypB) <-
        case hypothesis of
            Fix
                ( ImpliesPattern Implies
                    { impliesFirst = a
                    , impliesSecond = b
                    }
                )
                -> return (a,b)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind2 ++ ".")
    testFormulaEquality
        hypA (nameInKind2 "A")
        patA (nameInKind1 "A")
    testFormulaEquality
        hypB (nameInKind2 "B")
        patB (nameInKind1 "B")

    withContext
        (  "comparing the pattern lists for #sigma1{...} and #sigma2{...} in "
        ++ kind1
        )
        (testExtraPatternsEquality patterns1 patterns2 idx 0)
    -- TODO: test the other term equality
  where
    kind1 = "(#sigma1{...}(...,A,...) -> #sigma2{...}(...,B,...)))"
    kind2 = "A -> B"
    nameInKind1 name = name ++ " in " ++ kind1
    nameInKind2 name = name ++ " in " ++ kind2
    nameInProposition name =
        name ++ " in framing(symbol, idx, hyp)"

checkExistence
    :: Variable Meta
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkExistence variable conclusion
  = do
    (var1, var2) <-
        case conclusion of
            Fix
                ( ExistsPattern Exists
                    { existsVariable = v1
                    , existsChild = Fix (VariablePattern v2)
                    }
                )
                -> return (v1, v2)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind1 ++ ".")
    testFormulaEquality
        var1 (nameInKind1 "x")
        variable (nameInProposition "variable")
    testFormulaEquality
        var2 (nameInKind1 "y")
        variable (nameInProposition "variable")
  where
    kind1 = "(exists x . y)"
    nameInKind1 name = name ++ " in " ++ kind1
    nameInProposition name = name ++ " in Exists(variable)"

data SingvarPhi = SingvarPhiSimple | SingvarPhiNegated

checkSingvar
    :: Variable Meta
    -> CommonMetaPattern
    -> [Int]
    -> [Int]
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkSingvar variable phi path1 path2 conclusion
  = do
    (psi1, psi2) <-
        case conclusion of
            Fix
                ( NotPattern Not
                    { notChild = Fix
                        (AndPattern And
                            { andFirst = a
                            , andSecond = b
                            }
                        )
                    }
                )
                -> return (a, b)
            _ -> koreFail
                    ("Expected a meta-pattern of the form " ++ kind1 ++ ".")
    withContext (nameInKind1 "psi1")
        (checkSingvarContext
            variable (nameInProposition "variable")
            phi (nameInProposition "phi") SingvarPhiSimple
            path1
            psi1
        )
    withContext (nameInKind1 "psi2")
        (checkSingvarContext
            variable (nameInProposition "variable")
            phi (nameInProposition "(not phi)") SingvarPhiNegated
            path2
            psi2
        )
  where
    kind1 = "(not (psi1 /\\ psi2))"
    nameInKind1 name = name ++ " from " ++ kind1
    nameInProposition name = name ++ " in Singvar(variable, phi, path1, path2)"

checkSingvarContext
    :: Variable Meta
    -> String
    -> CommonMetaPattern
    -> String
    -> SingvarPhi
    -> [Int]
    -> CommonMetaPattern
    -> Either (Error MLError) ()
checkSingvarContext
    variable variableName phi phiName SingvarPhiSimple [] formula
  = do
    (var, psi) <-
        case formula of
            Fix
                (AndPattern And
                    { andFirst = Fix (VariablePattern v)
                    , andSecond = p
                    }
                )
                -> return (v, p)
            _ -> koreFail
                ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        var (nameInKind "x")
        variable variableName
    testFormulaEquality
        psi (nameInKind "psi")
        phi phiName
  where
    kind = "(x /\\ psi)"
    nameInKind name = name ++ " in " ++ kind
checkSingvarContext
    variable variableName phi phiName SingvarPhiNegated [] formula
  = do
    (var, psi) <-
        case formula of
            Fix
                (AndPattern And
                    { andFirst = Fix (VariablePattern v)
                    , andSecond = Fix
                        (NotPattern Not { notChild = p })
                    }
                )
                -> return (v, p)
            _ -> koreFail
                ("Expected a meta-pattern of the form " ++ kind ++ ".")
    testFormulaEquality
        var (nameInKind "x")
        variable variableName
    testFormulaEquality
        psi (nameInKind "psi")
        phi phiName
  where
    kind = "(x /\\ (not psi))"
    nameInKind name = name ++ " in " ++ kind
checkSingvarContext
    variable variableName phi phiName negated (pathItem:path) formula
  = do
    patterns <-
        case formula of
            Fix
                (ApplicationPattern Application
                    { applicationChildren = p }
                )
                -> return p
            _ -> koreFail
                ("Expected a meta-pattern of the form " ++ kind ++ ".")
    koreFailWhen (pathItem < 0)
        ("Negative path item: " ++ show pathItem ++ ".")
    koreFailWhen (pathItem >= length patterns)
        (  "Path item ("
        ++ show pathItem
        ++ ") must be lower than the actual pattern count ("
        ++ show (length patterns)
        ++ ")."
        )
    let child = patterns !! pathItem
    withContext ("Child #" ++ show pathItem)
        (checkSingvarContext
            variable variableName phi phiName negated path child
        )
  where
    kind = "sigma{...}(patterns)"

testExtraPatternsEquality
    :: [CommonMetaPattern]
    -> [CommonMetaPattern]
    -> Int
    -> Int
    -> Either (Error MLError) ()
testExtraPatternsEquality [] [] _ _ = return ()
testExtraPatternsEquality [] _ _ _ = koreFail "First pattern list too short"
testExtraPatternsEquality _ [] _ _ = koreFail "Second pattern list too short"
testExtraPatternsEquality (_:xs) (_:ys) 0 current =
    testExtraPatternsEquality xs ys (-1) (current + 1)
testExtraPatternsEquality (x:xs) (y:ys) n current = do
    testFormulaEquality
        x ("pattern #" ++ show current ++ " in the first list")
        y ("pattern #" ++ show current ++ " in the second list")
    testExtraPatternsEquality xs ys (n-1) (current + 1)

testFormulaEquality
    :: (Eq p, Unparse p)
    => p -> String
    -> p -> String
    -> Either (Error MLError) ()
testFormulaEquality phi phiName psi psiName = do
    koreFailWhen (phi /= psi)
        (  "Expected " ++ phiName
        ++ " to be equal to " ++ psiName
        ++ ", but the former is\n"
        ++ unparseToString phi
        ++ "\nwhile the latter is\n"
        ++ unparseToString psi
        )
    return ()
