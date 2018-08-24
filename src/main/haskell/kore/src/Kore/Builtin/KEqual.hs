{- |
Module      : Kore.Builtin.KEqual
Description : Built-in KEQUAL operations
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.KEqual as KEqual
@
 -}
module Kore.Builtin.KEqual
    ( symbolVerifiers
    , builtinFunctions
    ) where

import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( MetaOrObject, Object )
import           Kore.AST.PureML
                 ( PureMLPattern )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Error
                 ( unificationToStepError )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..), AttemptedFunction (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr (..) )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier, SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Unifier
                 ( unificationProcedure )
import           Kore.Unparser.Unparse
                 ( unparseToString )


groundObjectSort :: String -> Kore.Sort Object
groundObjectSort name =
    Kore.SortActualSort
        Kore.SortActual
        { sortActualName =
            Kore.Id
            { getId = name
            , idLocation = Kore.AstLocationImplicit
            }
        , sortActualSorts = []
        }


{- | K Sort
 -}
kSort :: Kore.Sort Object
kSort = groundObjectSort "SortK"

{- | Bool Sort
 -}
boolSort :: Kore.Sort Object
boolSort = groundObjectSort "SortBool"

{- | Verify that the sort is the @SortK@.

 -}
assertKSort :: Builtin.SortVerifier
assertKSort _ sort =
    Kore.Error.koreFailWhen (sort /= kSort)
        ("Sort '" ++ unparseToString sort ++ "' is not SortK")

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ("KEQUAL.eq", Builtin.verifySymbol Bool.assertSort [assertKSort, assertKSort])
    , ("KEQUAL.neq", Builtin.verifySymbol Bool.assertSort [assertKSort, assertKSort])
    ]

{- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
    [ ("KEQUAL.eq", keq)
    , ("KEQUAL.neq", kneq)
    ]

keq :: Builtin.Function
keq = ApplicationFunctionEvaluator (evalKEq True False)

kneq :: Builtin.Function
kneq = ApplicationFunctionEvaluator (evalKEq False True)

evalKEq
    :: Bool
    -> Bool
    -> MetadataTools Object StepperAttributes
    -> PureMLPatternSimplifier Object Kore.Variable
    -> Kore.Application Object (PureMLPattern Object Kore.Variable)
    -> Simplifier
        ( AttemptedFunction Object Kore.Variable
        , SimplificationProof Object
        )
evalKEq true false tools _ pat =
    case pat of
        Kore.Application _ [t1, t2] -> evalEq t1 t2
        _ -> failedToEval
  where
    evalEq t1 t2 =
        case unificationProcedure tools t1 t2 of
            Right (subst, predicate, _)
                | Predicate.isFalse predicate ->
                    trivialEvalResult (Bool.asPattern boolSort false)
                | null subst -> trivialEvalResult (Bool.asPattern boolSort true)
                | otherwise -> failedToEval
            Left err -> case unificationToStepError () (Left err) of
                Right () -> trivialEvalResult (Bool.asPattern boolSort false)
                Left _ -> failedToEval

failedToEval
    :: Simplifier
         (AttemptedFunction level1 variable, SimplificationProof level2)
failedToEval = pure (NotApplicable, SimplificationProof)

trivialEvalResult
    :: (Applicative f, MetaOrObject level1)
    => PureMLPattern level1 variable
    -> f (AttemptedFunction level1 variable, SimplificationProof level2)
trivialEvalResult p =
    pure (Applied (MultiOr [trivialExpandedPattern p]), SimplificationProof)

trivialExpandedPattern
    :: MetaOrObject level
    => PureMLPattern level var
    -> ExpandedPattern level var
trivialExpandedPattern p =
    ExpandedPattern p Predicate.makeTruePredicate []
