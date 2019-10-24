{-|
Module      : Kore.Step.Simplification.Exists
Description : Tools for Exists pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Exists
    ( simplify
    , makeEvaluate
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Map.Strict as Map
import GHC.Stack
    ( HasCallStack
    )

import Branch
    ( BranchT
    )
import qualified Branch
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.OrPredicate as OrPredicate
    ( fromPredicate
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( splitTerm
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( ElementVariable
    , pattern Equals_
    , Exists (Exists)
    , InternalVariable
    , Sort
    , TermLike
    , mkExists
    , withoutFreeVariable
    )
import qualified Kore.Internal.TermLike as TermLike
    ( hasFreeVariable
    , hasFreeVariable
    , markSimplified
    , substitute
    , withoutFreeVariable
    )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Sort
    ( predicateSort
    )
import Kore.Step.Axiom.Matcher
    ( matchIncremental
    )
import qualified Kore.Step.Simplification.AndPredicates as And
    ( simplifyEvaluatedMultiPredicate
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplify
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify
    ( runUnifierT
    )
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )


-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Exists' pattern with an 'OrPattern'
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
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Exists Sort variable (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify Exists { existsVariable, existsChild } =
    simplifyEvaluated existsVariable existsChild

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Exists Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of a 'variable' and an 'OrPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Attribute.Pattern' annotation
will eventually cache information besides the pattern sort, which will make it
even more useful to carry around.

-}
simplifyEvaluated
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => ElementVariable variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated variable simplified
  | OrPattern.isTrue simplified  = return simplified
  | OrPattern.isFalse simplified = return simplified
  | otherwise = do
    evaluated <- traverse (makeEvaluate variable) simplified
    return (OrPattern.flatten evaluated)

{-| evaluates an 'Exists' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => ElementVariable variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate variable original
  = fmap OrPattern.fromPatterns $ Branch.gather $ do
    normalized <- simplifyPredicate original
    let Conditional { substitution = normalizedSubstitution } = normalized
    case splitSubstitution variable normalizedSubstitution of
        (Left boundTerm, freeSubstitution) ->
            makeEvaluateBoundLeft
                variable
                boundTerm
                normalized { Conditional.substitution = freeSubstitution }
        (Right boundSubstitution, freeSubstitution) -> do
            matched <- Monad.Trans.lift $ matchesToVariableSubstitution
                variable
                normalized { Conditional.substitution = boundSubstitution }
            if matched
                then return normalized
                    { Conditional.predicate = Syntax.Predicate.makeTruePredicate
                    , Conditional.substitution = freeSubstitution
                    }
                else makeEvaluateBoundRight
                    variable
                    freeSubstitution
                    normalized { Conditional.substitution = boundSubstitution }

matchesToVariableSubstitution
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => ElementVariable variable
    -> Pattern variable
    -> simplifier Bool
matchesToVariableSubstitution
    variable
    Conditional {term, predicate, substitution = boundSubstitution}
  | Equals_ _sort1 _sort2 first second <-
        Syntax.Predicate.fromPredicate predicateSort predicate
  , Substitution.null boundSubstitution
  , not (TermLike.hasFreeVariable (ElemVar variable) term)
  = do
    matchResult <- runUnifierT $ matchIncremental first second
    case matchResult of
        Left _ -> return False
        Right results ->
            return (all (singleVariableSubstitution variable) results)

matchesToVariableSubstitution _ _ = return False

singleVariableSubstitution
    :: InternalVariable variable
    => ElementVariable variable -> Predicate variable -> Bool
singleVariableSubstitution
    variable
    Conditional
        { term = ()
        , predicate = Syntax.Predicate.PredicateTrue
        , substitution
        }
  = case Substitution.unwrap substitution of
    [] -> (error . unlines)
        [ "This should not happen. This is called with matching results, and,"
        , "if matching can be resolved without generating predicates or "
        , "substitutions, then the equality should have already been resolved."
        ]
    [(substVariable, substTerm)]
        | substVariable == ElemVar variable ->
            TermLike.withoutFreeVariable substVariable substTerm
                True
    _ -> False
singleVariableSubstitution _ _ = False

{- | Existentially quantify a variable in the given 'Pattern'.

The variable was found on the left-hand side of a substitution and the given
term will be substituted everywhere. The variable may occur anywhere in the
'term' or 'predicate' of the 'Pattern', but not in the
'substitution'. The quantified variable must not occur free in the substituted
 term; an error is thrown if it is found.  The final result will not contain the
 quantified variable and thus the quantifier will actually be omitted.

See also: 'quantifyPattern'

 -}
makeEvaluateBoundLeft
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => ElementVariable variable  -- ^ quantified variable
    -> TermLike variable  -- ^ substituted term
    -> Pattern variable
    -> BranchT simplifier (Pattern variable)
makeEvaluateBoundLeft variable boundTerm normalized
  = withoutFreeVariable (ElemVar variable) boundTerm $ do
        let
            boundSubstitution = Map.singleton (ElemVar variable) boundTerm
            substituted =
                normalized
                    { Conditional.term =
                        TermLike.substitute boundSubstitution
                        $ Conditional.term normalized
                    , Conditional.predicate =
                        Syntax.Predicate.substitute boundSubstitution
                        $ Conditional.predicate normalized
                    }
        orPattern <- Monad.Trans.lift $ Pattern.simplify substituted
        Branch.scatter (MultiOr.extractPatterns orPattern)

{- | Existentially quantify a variable in the given 'Pattern'.

The variable does not occur in the any equality in the free substitution. The
variable may occur anywhere in the 'term' or 'predicate' of the
'Pattern', but only on the right-hand side of an equality in the
'substitution'.

See also: 'quantifyPattern'

 -}
makeEvaluateBoundRight
    :: forall variable simplifier
    . (SimplifierVariable variable, MonadSimplify simplifier)
    => ElementVariable variable  -- ^ variable to be quantified
    -> Substitution variable  -- ^ free substitution
    -> Pattern variable  -- ^ pattern to quantify
    -> BranchT simplifier (Pattern variable)
makeEvaluateBoundRight variable freeSubstitution normalized = do
    orPredicate <- Monad.Trans.lift $ And.simplifyEvaluatedMultiPredicate
        (MultiAnd.make
            [   OrPredicate.fromPredicate quantifyPredicate
            ,   OrPredicate.fromPredicate
                    (Predicate.fromSubstitution freeSubstitution)
            ]
        )
    predicate <- Branch.scatter orPredicate
    let simplifiedPattern = quantifyTerm `Conditional.withCondition` predicate
    TopBottom.guardAgainstBottom simplifiedPattern
    return simplifiedPattern
  where
    (quantifyTerm, quantifyPredicate) = Pattern.splitTerm
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
splitSubstitution
    :: (SimplifierVariable variable, HasCallStack)
    => ElementVariable variable
    -> Substitution variable
    ->  ( Either (TermLike variable) (Substitution variable)
        , Substitution variable
        )
splitSubstitution variable substitution =
    (bound, independent)
  where
    reversedSubstitution =
        Substitution.reverseIfRhsIsVar (ElemVar variable) substitution
    (dependent, independent) =
        Substitution.partition hasVariable reversedSubstitution
    hasVariable variable' term =
        ElemVar variable == variable'
        || TermLike.hasFreeVariable (ElemVar variable) term
    bound =
        maybe (Right dependent) Left
        $ Map.lookup (ElemVar variable) (Substitution.toMap dependent)

{- | Existentially quantify the variable in a 'Pattern'.

The substitution is assumed to not depend on the quantified variable.
The quantifier is lowered onto the 'term' or 'predicate' alone, or omitted,
if possible.

 -}
quantifyPattern
    :: InternalVariable variable
    => ElementVariable variable
    -> Pattern variable
    -> Pattern variable
quantifyPattern variable original@Conditional { term, predicate, substitution }
  | quantifyTerm, quantifyPredicate
  = (error . unlines)
    [ "Quantifying both the term and the predicate probably means that there's"
    , "an error somewhere else."
    , "variable=" ++ unparseToString variable
    , "patt=" ++ unparseToString original
    ]
  | quantifyTerm = TermLike.markSimplified . mkExists variable <$> original
  | quantifyPredicate =
    Conditional.withCondition term
    $ Predicate.fromPredicate . Syntax.Predicate.markSimplified
    -- TODO (thomas.tuegel): This may not be fully simplified: we have not used
    -- the And simplifier on the predicate.
    $ Syntax.Predicate.makeExistsPredicate variable predicate'
  | otherwise = original
  where
    quantifyTerm = TermLike.hasFreeVariable (ElemVar variable) term
    predicate' =
        Syntax.Predicate.makeAndPredicate predicate
        $ Syntax.Predicate.fromSubstitution substitution
    quantifyPredicate =
        Syntax.Predicate.hasFreeVariable (ElemVar variable) predicate'
