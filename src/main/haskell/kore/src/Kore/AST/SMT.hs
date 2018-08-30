module Kore.AST.SMT where

import Data.SBV

import Kore.AST.Common
import Kore.AST.Kore ( CommonKorePattern, UnifiedPattern )
import Kore.AST.MetaOrObject

import           Data.Foldable
                 ( fold )
import           Data.Functor.Foldable
                 ( Fix, cata )
import qualified Data.Set as Set
import qualified Data.Map as Map

import Kore.AST.MLPatterns
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.ASTTraversals
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.Variables.Free

-- To use this:
-- The "iv1" ... "iv9" variables contain various Kore boolean expressions.
--   - iv1  encodes "a -> a"
--   - iv2  encodes "a -> b"
--   - iv3  encodes "(a ^ (a -> b)) -> b"
--   - iv4  encodes "(a \/ (a -> b)) -> b"
--
-- Use `runProof iv1`, etc. to pass these to the constraint
-- solver.  `runProof` will extract the variable names, call `buildProof`
-- to construct the SBV equivalent boolean expression, and then pass its
-- negation to the constraint solver.

-- Right now, it assumes all variables are booleans.  Next step, support
-- integer sorts, and add more logical connectives.

{-| 'buildProof' -- creates an SBV term to pass to the verifier
    inputs:
      Map String SBool   - a map from variable names to SBools
      PureMLPattern      - the Kore constraint we want to check
    output:
      SBool              - a boolean expression for the constraint solver
    use:
      This is called by the `runProof` function.
  -}
buildProof
    :: Map.Map String SBool -> PureMLPattern Object Variable  -> SBool
buildProof varMap pat = patternBottomUpVisitor makeProofVisitor pat
    where
      makeProofVisitor :: Pattern level Variable SBool -> SBool
      makeProofVisitor (VariablePattern v) =
          case Map.lookup (getId . variableName $ v) varMap of
            Just s -> s
            Nothing -> error $ "Variable not defined."
      makeProofVisitor (ImpliesPattern i@(Implies {})) =
          (impliesFirst i) ==> (impliesSecond i)
      makeProofVisitor (AndPattern i@(And {})) = 
          (andFirst i) &&& (andSecond i)
      makeProofVisitor (OrPattern i@(Or {})) = 
          (orFirst i) ||| (orSecond i)
      makeProofVisitor (NotPattern i@(Not {})) = 
          bnot (notChild i)


-- Get the name of a variable from a Unified var Pattern
getName :: Unified Variable -> String
getName (UnifiedObject v@(Variable{})) = (getId . variableName) v

{-| 'runProof' creates a variable mapping and calls `buildProof` to
     get an SBV expression to check with the SMT solver. -}

runProof
    :: PureMLPattern Object Variable  -> IO AllSatResult -- Symbolic SBool
runProof pat = allSatWith myz3 $ do
      smtVars <- sBools varNames
      let varMap = Map.fromList (zip varNames smtVars)
      let proof = buildProof varMap pat
      solve [bnot proof]

    where
      varNames :: [String]
      varNames = Prelude.map getName (Set.toList (freeVariables pat))

-- Some toy examples to test things

boolVSort :: Sort Object
boolVSort =  SortVariableSort (SortVariable {getSortVariable = Id {getId = "Bool", idLocation = AstLocationNone }})

boolASort :: Sort Object
boolASort =  SortActualSort (SortActual { sortActualName = Id {getId= "Bool", idLocation = AstLocationNone },
                                          sortActualSorts = []})

mkBoolVar :: String -> Variable Object
mkBoolVar name =
   Kore.AST.Common.Variable { variableName = Id {getId = name, idLocation = AstLocationNone },
                              variableSort = boolVSort }

v1 = Var_ $ mkBoolVar "a1"
v2 = Var_ $ mkBoolVar "a2"

iv1 = Implies_ boolASort v1 v1
iv2 = Implies_ boolASort v1 v2
iv3 = Implies_ boolASort (And_ boolASort v1 iv2) v2
iv4 = Implies_ boolASort (Or_ boolASort v1 iv2) v2
iv5 = Implies_ boolASort (Or_ boolASort v1 iv2) (Not_ boolASort v2)
iv6 = Not_ boolASort iv4

myz3 = z3 { solver = (solver z3) { executable = "/run/current-system/sw/bin/z3"}}

-- Some examples of calling the SMT solver directly, for reference.
-- Delete them before integration.

solveI1 :: IO AllSatResult
solveI1 = allSatWith myz3 $ do
       [a1,a2] <- sBools ["a1","a2"]
       solve [ a1 ==> a2 ]

proofI1 = do
       [a1,a2] <- sBools ["a1","a2"]
       solve [bnot (a1 ==> a2) ]


proof v1 v2 = allSatWith myz3 $ do
       vars <- sBools ["a","b"]
       solve [bnot ((vars !! v1) ==> (vars !! v2)) ]


fbpuzzle :: IO AllSatResult
fbpuzzle = allSatWith myz3 $ do
       [coke,burger,fries] <- sIntegers ["coke","burger","fries"]
       constrain $ coke + coke + coke .== 30
       constrain $ coke + burger + burger .== 20
       constrain $ burger + fries + fries .== 9
       solve [ ]
