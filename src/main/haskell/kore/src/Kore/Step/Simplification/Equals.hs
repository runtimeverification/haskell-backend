{-|
Module      : Kore.Simplification.Equals
Description : Tools for Equals pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Equals
    ( makeEvaluate
    , simplify
    ) where

import Control.Monad
       ( foldM, zipWithM )
import Data.Either
       ( isRight )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Equals (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_, pattern CharLiteral_, pattern DV_,
                 pattern StringLiteral_, pattern Top_, pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )
import           Kore.Step.PatternAttributes
                 ( isFunctionPattern, isFunctionalPattern )
import qualified Kore.Step.Simplification.And as And
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), Simplifier )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplifyEvaluated )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Int
                 ( IntVariable (..) )

{-|'simplify' simplifies an 'Equals' pattern made of 'OrOfExpandedPattern's.

This uses the following simplifications
(t = term, s = substitution, p = predicate):

* Equals(a, a) = true
* Equals(t1 and p1 and s1, t2 and p2 and s2) =
    Or(
        And(
            Equals(t1, t2)
            And(ceil(t1) and p1 and s1, ceil(t2) and p2 and s2))
        And(not(ceil(t1) and p1 and s1), not(ceil(t2) and p2 and s2))
    )
    + If t1 and t2 can't be bottom, then this becomes
      Equals(t1 and p1 and s1, t2 and p2 and s2) =
        Or(
            And(
                Equals(t1, t2)
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the two terms are constructors, then this becomes
      Equals(
        constr1(t1, t2, ...) and p1 and s1,
        constr2(t1', t2', ...) and p2 and s2)
        = Or(
            and(
                (p1 and s2) iff (p2 and s2),
                constr1 == constr2,
                ceil(constr1(t1, t2, ...), constr2(t1', t2', ...))
                Equals(t1, t1'), Equals(t2, t2'), ...
                )
            and(
                not(ceil(constr1(t1, t2, ...)) and p1 and s1),
                not(ceil(constr2(t1', t2', ...)), p2 and s2)
                )
        )
      Note that when expanding Equals(t1, t1') recursively we don't need to
      put the ceil conditions again, since we already asserted that.
      Also note that ceil(constr(...)) is simplifiable.
    + If the first term is a variable and the second is functional,
      then we get a substitution:
        Or(
            And(
                [t1 = t2]
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the terms are Top, this becomes
      Equals(p1 and s1, p2 and s2) = Iff(p1 and s1, p2 and s2)
    + If the predicate and substitution are Top, then the result is just
      Equals(t1, t2)

Normalization of the compared terms is not implemented yet, so
Equals(a and b, b and a) will not be evaluated to Top.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> Equals level (OrOfExpandedPattern level domain variable)
    -> Simplifier
        ( OrOfExpandedPattern level domain variable
        , SimplificationProof level
        )
simplify
    tools
    Equals
        { equalsFirst = first
        , equalsSecond = second
        }
  =
    simplifyEvaluated tools first second

simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level domain variable
    -> OrOfExpandedPattern level domain variable
    -> Simplifier
        (OrOfExpandedPattern level domain variable, SimplificationProof level)
simplifyEvaluated tools first second
  | first == second =
    return (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluate tools firstP secondP
        _ ->
            give (MetadataTools.sortTools tools)
                $ makeEvaluate tools
                    (OrOfExpandedPattern.toExpandedPattern first)
                    (OrOfExpandedPattern.toExpandedPattern second)
  where
    firstPatterns = OrOfExpandedPattern.extractPatterns first
    secondPatterns = OrOfExpandedPattern.extractPatterns second

{-| evaluates an 'Equals' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level domain variable
    -> ExpandedPattern level domain variable
    -> Simplifier
        (OrOfExpandedPattern level domain variable, SimplificationProof level)
makeEvaluate
    tools
    first@ExpandedPattern
        { term = Top_ _ }
    second@ExpandedPattern
        { term = Top_ _ }
  =
    let
        (result, _proof) = give (MetadataTools.sortTools tools )
            $ Iff.makeEvaluate first second
    in
        return (result, SimplificationProof)
makeEvaluate
    tools
    ExpandedPattern
        { term = firstTerm
        , predicate = PredicateTrue
        , substitution = []
        }
    ExpandedPattern
        { term = secondTerm
        , predicate = PredicateTrue
        , substitution = []
        }
  =
    makeEvaluateTermsAssumesNoBottom tools firstTerm secondTerm
makeEvaluate
    tools
    first@ExpandedPattern
        { term = firstTerm }
    second@ExpandedPattern
        { term = secondTerm }
  = do
    let
        (firstCeil, _proof1) =
            Ceil.makeEvaluate tools
                first
                    { ExpandedPattern.term =
                        if termsAreEqual then mkTop else firstTerm
                    }
        (secondCeil, _proof2) =
            Ceil.makeEvaluate tools
                second
                    { ExpandedPattern.term =
                        if termsAreEqual then mkTop else secondTerm
                    }
        (firstCeilNegation, _proof3) =
            give sortTools $ Not.simplifyEvaluated firstCeil
        (secondCeilNegation, _proof4) =
            give sortTools $ Not.simplifyEvaluated secondCeil
    (termEquality, _proof) <-
        makeEvaluateTermsAssumesNoBottom tools firstTerm secondTerm
    (negationAnd, _proof) <-
        And.simplifyEvaluated tools firstCeilNegation secondCeilNegation
    (ceilAnd, _proof) <- And.simplifyEvaluated tools firstCeil secondCeil
    (equalityAnd, _proof) <-
        And.simplifyEvaluated tools termEquality ceilAnd
    let
        (finalOr, _proof) =
            give sortTools $ Or.simplifyEvaluated equalityAnd negationAnd
    return (finalOr, SimplificationProof)
  where
    sortTools = MetadataTools.sortTools tools
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Simplifier
        (OrOfExpandedPattern level domain variable, SimplificationProof level)
makeEvaluateTermsAssumesNoBottom
    tools first second
  | first == second =
    return
        ( OrOfExpandedPattern.make
            [ ExpandedPattern
                { term = mkTop
                , predicate = makeTruePredicate
                , substitution = []
                }
            ]
        , SimplificationProof
        )
  | otherwise =
    -- Writing this the normal way seems to be too much for Haskell's
    -- pattern matching, this is a workaround.
    firstMaybe
        [ differentCharLiterals first second
        , differentStringLiterals first second
        , differentDomainValues first second
        , variableEqualsFunctional tools first second
        , functionalEqualsVariable tools first second
        , constructorAtTheTop tools first second
        ]
        ( return
            ( OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = give (MetadataTools.sortTools tools)
                        $ makeEqualsPredicate first second
                    , substitution = []
                    }
                ]
            , SimplificationProof
            )
        )

differentCharLiterals
    :: PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
differentCharLiterals
    (CharLiteral_ _) (CharLiteral_ _)
  =
    Just (return (OrOfExpandedPattern.make [], SimplificationProof))
differentCharLiterals _ _ = Nothing

differentStringLiterals
    :: PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
differentStringLiterals
    (StringLiteral_ _) (StringLiteral_ _)
  =
    Just (return (OrOfExpandedPattern.make [], SimplificationProof))
differentStringLiterals _ _ = Nothing

differentDomainValues
    :: PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
differentDomainValues
    (DV_ _ (StringLiteral_ _))
    (DV_ _ (StringLiteral_ _))
    = Just (return (OrOfExpandedPattern.make [], SimplificationProof))
differentDomainValues _ _ = Nothing

variableEqualsFunctional
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
variableEqualsFunctional
    tools (Var_ var) term
  | isFunctional tools term || isFunction tools term
  =
    Just
        (return
            ( OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(var, term)]
                    }
                ]
            , SimplificationProof
            )
        )
variableEqualsFunctional _ _ _ = Nothing

functionalEqualsVariable
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
functionalEqualsVariable
    tools term (Var_ var)
  | isFunctional tools term || isFunction tools term
  =
    Just
        (return
            ( OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = [(var, term)]
                    }
                ]
            , SimplificationProof
            )
        )
functionalEqualsVariable _ _ _ = Nothing

constructorAtTheTop
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> PureMLPattern level domain variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
        )
constructorAtTheTop
    tools
    (App_ firstSymbol firstChildren)
    (App_ secondSymbol secondChildren)
  | isConstructor' firstSymbol && isConstructor' secondSymbol
  = Just $
    if firstSymbol == secondSymbol
        then do -- IntCounter monad
            childrenEquals <-
                zipWithM
                    (makeEvaluateTermsAssumesNoBottom tools)
                    firstChildren
                    secondChildren
            (childrenAnd, _proof) <-
                foldM
                    (combineWithAnd tools)
                    ( OrOfExpandedPattern.make [ExpandedPattern.top]
                    , SimplificationProof
                    )
                    childrenEquals
            return (childrenAnd, SimplificationProof)
        else return (OrOfExpandedPattern.make [], SimplificationProof)
  where
    -- TODO: Extract this somewhere.
    isConstructor' symbolHead =
        StepperAttributes.isConstructor
            (MetadataTools.attributes tools symbolHead)
    combineWithAnd
        ::  ( MetaOrObject level
            , SortedVariable variable
            , Show (variable level)
            , Ord (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , IntVariable variable
            , Hashable variable
            )
        => MetadataTools level StepperAttributes
        -> (OrOfExpandedPattern level domain variable, SimplificationProof level)
        -> (OrOfExpandedPattern level domain variable, SimplificationProof level)
        -> Simplifier
            (OrOfExpandedPattern level domain variable, SimplificationProof level)
    combineWithAnd tools' (thing1, _proof1) (thing2, _proof2) =
        And.simplifyEvaluated tools' thing1 thing2
constructorAtTheTop _ _ _ = Nothing


firstMaybe :: [Maybe a] -> a -> a
firstMaybe [] x = x
firstMaybe (Just x : _) _ = x
firstMaybe (_ : xs) x = firstMaybe xs x

-- TODO: Move these somewhere reasonable and remove all of their other
-- definitions.
isFunction
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Bool
isFunction tools term =
    isRight (isFunctionPattern tools term)

isFunctional
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Bool
isFunctional tools term =
    isRight (isFunctionalPattern tools term)
