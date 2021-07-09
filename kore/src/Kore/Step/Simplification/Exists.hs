{- |
Module      : Kore.Step.Simplification.Exists
Description : Tools for Exists pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Exists (
    simplify,
    makeEvaluate,
    simplifyEvaluated,
) where

import Control.Monad (
    foldM,
 )
import Data.List (
    sortBy,
 )
import qualified Data.Map.Strict as Map
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiAnd as MultiAnd (
    make,
 )
import qualified Kore.Internal.OrCondition as OrCondition (
    fromCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    splitTerm,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike (
    ElementVariable,
    Exists (Exists),
    SomeVariableName,
    Sort,
    TermLike,
    Variable (..),
    mkExists,
    retractElementVariable,
    withoutFreeVariable,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Axiom.Matcher (
    matchIncremental,
 )
import qualified Kore.Step.Simplification.AndPredicates as And (
    simplifyEvaluatedMultiPredicate,
 )
import qualified Kore.Step.Simplification.Pattern as Pattern (
    makeEvaluate,
 )
import Kore.Step.Simplification.Simplify
import Kore.Substitute
import qualified Kore.TopBottom as TopBottom
import Kore.Unparser
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore

-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.

{- |'simplify' simplifies an 'Exists' pattern with an 'OrPattern'
child.

The simplification of exists x . (pat and pred and subst) is equivalent to:

* If the subst contains an assignment y=x, then reverse that and continue with
  the next step.
* If the subst contains an assignment for x, then substitute that in pat and
  pred, reevaluate them and return
  (reevaluated-pat and reevaluated-pred and subst-without-x).
* Otherwise, if x occurs free in pred, but not in the term or the subst,
  and pred has the form phi=psi, then we try to match phi and psi. If the
  match result has the form `x=alpha`, then we return `top`.
  ( exists x . f(x)=f(alpha) is equivalent to
    exists x . (x=alpha) or (not(x==alpha) and f(x)=f(alpha)), which becomes
    (exists x . (x=alpha))
      or (exists x . (not(x==alpha) and f(x)=f(alpha)).
    But exists x . (x=alpha) == top, so the original term is top.
  )
* Let patX = pat if x occurs free in pat, top otherwise
      pat' = pat if x does not occur free in pat, top otherwise
  Let predX, pred' be defined in a similar way.
  Let substX = those substitutions in which x occurs free,
      subst' = the other substitutions
  + If patX is not top, then return
    (exists x . patX and predX and substX) and pred' and subst'
  + otherwise, return
    (pat' and (pred' and (exists x . predX and substX)) and subst')
-}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Exists Sort RewritingVariableName (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition Exists{existsVariable, existsChild} =
    simplifyEvaluated sideCondition existsVariable existsChild

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Exists Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of a 'variable' and an 'OrPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Attribute.Pattern' annotation
will eventually cache information besides the pattern sort, which will make it
even more useful to carry around.

-}
simplifyEvaluated ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    ElementVariable RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyEvaluated sideCondition variable simplified
    | OrPattern.isTrue simplified = return simplified
    | OrPattern.isFalse simplified = return simplified
    | otherwise =
        OrPattern.flatten
            <$> OrPattern.traverse
                (makeEvaluate sideCondition [variable])
                simplified

{- | Evaluates a multiple 'Exists' given a pattern and a list of
variables which are existentially quantified in the pattern. This
also sorts the list of variables to ensure that those which are present
in the substitution are evaluated with the pattern first.

See 'simplify' for detailed documentation.
-}
makeEvaluate ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    [ElementVariable RewritingVariableName] ->
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
makeEvaluate sideCondition variables original = do
    let sortedVariables = sortBy substVariablesFirst variables
    foldM (flip makeEvaluateWorker) original sortedVariables
        & OrPattern.observeAllT
  where
    makeEvaluateWorker ::
        ElementVariable RewritingVariableName ->
        Pattern RewritingVariableName ->
        LogicT simplifier (Pattern RewritingVariableName)
    makeEvaluateWorker variable original' = do
        normalized <- simplifyCondition sideCondition original'
        let Conditional{substitution = normalizedSubstitution} = normalized
        case splitSubstitution variable normalizedSubstitution of
            (Left boundTerm, freeSubstitution) ->
                makeEvaluateBoundLeft
                    sideCondition
                    variable
                    boundTerm
                    normalized{Conditional.substitution = freeSubstitution}
            (Right boundSubstitution, freeSubstitution) -> do
                matched <-
                    normalized
                        { Conditional.substitution = boundSubstitution
                        }
                        & matchesToVariableSubstitution sideCondition variable
                        & lift
                if matched
                    then
                        return
                            normalized
                                { Conditional.predicate = Predicate.makeTruePredicate
                                , Conditional.substitution = freeSubstitution
                                }
                    else
                        makeEvaluateBoundRight
                            sideCondition
                            variable
                            freeSubstitution
                            normalized
                                { Conditional.substitution = boundSubstitution
                                }

    substVariablesFirst ::
        ElementVariable RewritingVariableName ->
        ElementVariable RewritingVariableName ->
        Ordering
    substVariablesFirst var1 var2
        | var1 `elem` substVariables
          , notElem var2 substVariables =
            LT
        | notElem var1 substVariables
          , var2 `elem` substVariables =
            GT
        | otherwise = EQ

    substVariables =
        mapMaybe
            retractElementVariable
            $ toList $
                Substitution.variables
                    (Conditional.substitution original)

-- TODO (andrei.burdusa): this function must go away
matchesToVariableSubstitution ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    ElementVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier Bool
matchesToVariableSubstitution
    sideCondition
    variable
    Conditional{term, predicate, substitution = boundSubstitution}
        | Predicate.PredicateEquals first second <- predicate
          , Substitution.null boundSubstitution
          , not (TermLike.hasFreeVariable (inject $ variableName variable) term) =
            do
                matchResultFS <- matchIncremental sideCondition first second
                matchResultSF <- matchIncremental sideCondition second first
                case matchResultFS <|> matchResultSF of
                    Just (Predicate.PredicateTrue, results) ->
                        return (singleVariableSubstitution variable results)
                    _ -> return False
        | otherwise = return False

singleVariableSubstitution ::
    ElementVariable RewritingVariableName ->
    Map.Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName) ->
    Bool
singleVariableSubstitution
    variable
    substitution
        | Map.null substitution =
            (error . unlines)
                [ "This should not happen. This is called with matching results, and,"
                , "if matching can be resolved without generating predicates or "
                , "substitutions, then the equality should have already been resolved."
                ]
        | Map.size substitution == 1 =
            case Map.lookup someVariableName substitution of
                Nothing -> False
                Just substTerm ->
                    TermLike.withoutFreeVariable someVariableName substTerm True
        | otherwise = False
      where
        someVariableName = inject (variableName variable)

{- | Existentially quantify a variable in the given 'Pattern'.

The variable was found on the left-hand side of a substitution and the given
term will be substituted everywhere. The variable may occur anywhere in the
'term' or 'predicate' of the 'Pattern', but not in the
'substitution'. The quantified variable must not occur free in the substituted
 term; an error is thrown if it is found.  The final result will not contain the
 quantified variable and thus the quantifier will actually be omitted.

See also: 'quantifyPattern'
-}
makeEvaluateBoundLeft ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    -- | quantified variable
    ElementVariable RewritingVariableName ->
    -- | substituted term
    TermLike RewritingVariableName ->
    Pattern RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
makeEvaluateBoundLeft sideCondition variable boundTerm normalized =
    withoutFreeVariable someVariableName boundTerm $ do
        let boundSubstitution = Map.singleton someVariableName boundTerm
            substituted =
                normalized
                    { Conditional.term =
                        substitute boundSubstitution $
                            Conditional.term normalized
                    , Conditional.predicate =
                        substitute boundSubstitution $
                            Conditional.predicate normalized
                    }
        orPattern <-
            lift $ Pattern.makeEvaluate sideCondition substituted
        Logic.scatter (toList orPattern)
  where
    someVariableName = inject (variableName variable)

{- | Existentially quantify a variable in the given 'Pattern'.

The variable does not occur in the any equality in the free substitution. The
variable may occur anywhere in the 'term' or 'predicate' of the
'Pattern', but only on the right-hand side of an equality in the
'substitution'.

See also: 'quantifyPattern'
-}
makeEvaluateBoundRight ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    -- | variable to be quantified
    ElementVariable RewritingVariableName ->
    -- | free substitution
    Substitution RewritingVariableName ->
    -- | pattern to quantify
    Pattern RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
makeEvaluateBoundRight sideCondition variable freeSubstitution normalized = do
    orCondition <-
        lift $
            And.simplifyEvaluatedMultiPredicate
                sideCondition
                ( MultiAnd.make
                    [ OrCondition.fromCondition quantifyCondition
                    , OrCondition.fromCondition
                        (Condition.fromSubstitution freeSubstitution)
                    ]
                )
    predicate <- Logic.scatter orCondition
    let simplifiedPattern = quantifyTerm `Conditional.withCondition` predicate
    TopBottom.guardAgainstBottom simplifiedPattern
    return simplifiedPattern
  where
    (quantifyTerm, quantifyCondition) =
        Pattern.splitTerm
            (quantifyPattern variable normalized)

{- | Split the substitution on the given variable.

The substitution must be normalized and the normalization state is preserved.

The result is a pair of:

* Either the term bound to the variable (if the variable is on the 'Left' side
  of a substitution) or the substitutions that depend on the variable (if the
  variable is on the 'Right' side of a substitution). (These conditions are
  mutually exclusive for a normalized substitution.)
* The substitutions that do not depend on the variable at all.
-}
splitSubstitution ::
    HasCallStack =>
    ElementVariable RewritingVariableName ->
    Substitution RewritingVariableName ->
    ( Either
        (TermLike RewritingVariableName)
        (Substitution RewritingVariableName)
    , Substitution RewritingVariableName
    )
splitSubstitution variable substitution =
    (bound, independent)
  where
    orderRenamedSubstitution =
        Substitution.orderRenameAndRenormalizeTODO
            someVariable
            substitution
    (dependent, independent) =
        Substitution.partition hasVariable orderRenamedSubstitution
    hasVariable variable' term =
        someVariable == variable'
            || TermLike.hasFreeVariable someVariableName term
    bound =
        maybe (Right dependent) Left $
            Map.lookup someVariableName (Substitution.toMap dependent)
    someVariable = inject variable
    someVariableName = variableName someVariable

{- | Existentially quantify the variable in a 'Pattern'.

The substitution is assumed to not depend on the quantified variable.
The quantifier is lowered onto the 'term' or 'predicate' alone, or omitted,
if possible.
-}
quantifyPattern ::
    ElementVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName
quantifyPattern variable original@Conditional{term, predicate, substitution}
    | quantifyTerm
      , quantifyPredicate =
        (error . unlines)
            [ "Quantifying both the term and the predicate probably means that there's"
            , "an error somewhere else."
            , "variable=" ++ unparseToString variable
            , "patt=" ++ unparseToString original
            ]
    | quantifyTerm = TermLike.markSimplified . mkExists variable <$> original
    | quantifyPredicate =
        Conditional.withCondition term $
            Condition.fromPredicate . Predicate.markSimplified
            -- TODO (thomas.tuegel): This may not be fully simplified: we have not used
            -- the And simplifier on the predicate.
            $
                Predicate.makeExistsPredicate variable predicate'
    | otherwise = original
  where
    someVariableName = inject (variableName variable)
    quantifyTerm = TermLike.hasFreeVariable someVariableName term
    predicate' =
        Predicate.makeAndPredicate predicate $
            Substitution.toPredicate substitution
    quantifyPredicate =
        Predicate.hasFreeVariable someVariableName predicate'
