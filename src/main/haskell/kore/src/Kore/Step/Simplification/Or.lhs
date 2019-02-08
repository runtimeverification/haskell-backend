% Or Simplification

== Header

\begin{code}
{-|
Module      : Kore.Step.Simplification.Or
Description : Tools for Or pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Or
    ( simplifyEvaluated
    , simplify
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Function as Function
import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( makeOrPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, merge )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser
\end{code}

== Driver

\begin{code}
{-|'simplify' simplifies an 'Or' pattern with 'OrOfExpandedPattern'
children by merging the two children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Or level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
\end{code}

`simplify` is a driver responsible for breaking down an `\or` pattern and
simplifying its children.

\begin{code}
simplify
    Or
        { orFirst = first
        , orSecond = second
        }
  =
    simplifyEvaluated first second

{-| simplifies an 'Or' given its two 'OrOfExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
\end{code}

**TODO** (virgil): Preserve pattern sorts under simplification.
One way to preserve the required sort annotations is to make `simplifyEvaluated`
take an argument of type
``` haskell
CofreeF (Or level) (Valid level) (OrOfExpandedPattern level variable)
```
instead of two `OrOfExpandedPattern` arguments. The type of `makeEvaluate` may
be changed analogously. The `Valid` annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

**TODO** (virgil): This should do all possible mergings, not just the first term
with the second.

\begin{code}
simplifyEvaluated first second

  | (head1 : tail1) <- OrOfExpandedPattern.extractPatterns first
  , (head2 : tail2) <- OrOfExpandedPattern.extractPatterns second
  , Just (result, proof) <- simplifySinglePatterns head1 head2
  = (OrOfExpandedPattern.make $ result : (tail1 ++ tail2), proof)

  | otherwise =
    ( OrOfExpandedPattern.merge first second
    , SimplificationProof
    )

  where
    simplifySinglePatterns first' second' =
        disjoinPredicates first' second' <|> topAnnihilates first' second'
\end{code}

== Disjoin predicates

\begin{code}
{- | Merge two configurations by the disjunction of their predicates.

This simplification case is only applied if the configurations have the same
'term'.

 -}
disjoinPredicates
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -- ^ Configuration
    -> ExpandedPattern level variable
    -- ^ Disjunction
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
\end{code}

When two configurations have the same substitution, it may be possible to
simplify the pair by disjunction of their predicates.
```
(             t₁, p₁, s) ∨ (             t₂, p₂, s)
([t₂ ∨ ¬t₂] ∧ t₁, p₁, s) ∨ ([t₁ ∨ ¬t₁] ∧ t₂, p₂, s)

(t₁ ∧ t₂, p₁ ∨ p₂, s) ∨ (¬t₂ ∧ t₁, p₁, s) ∨ (¬t₁ ∧ t₂, p₂, s)
```
It is useful to apply the above equality when
```
¬t₂ ∧ t₁ = ¬t₁ ∧ t₂ = ⊥
t₁ = t₂
```
so that
```
(t₁, p₁, s) ∨ (t₂, p₂, s) = (t₁ ∧ t₂, p₁ ∨ p₂, s)
  where
    t₁ = t₂.
```

**Note**: [Weakening predicates]

Phillip: It is not clear that we should *ever* apply this simplification.  We
attempt to refute the conditions on configurations using an external solver to
reduce the configuration space for execution.  The solver operates best when it
has the most information, and the predicate `p₁ ∨ p₂` is strictly weaker than
either `p₁` or `p₂`.

Virgil: IIRC the main reason for having this was to be able to use some
assumptions on the pattern form at a time when it wasn't obvious that we needed
full generality.

That being said: for now, it's obvious that we want to split the configuration
when we have an or between terms or substitutions (though that might change at
some point), but, for predicates, it might be better to let the external solver
handle this than for us to handle one more configuration, that will potentially
be split into many other configurations. Or it may be worse, I don't know.

To make it short: I agree with this, but I wanted to say the above in case it's
useful.

\begin{code}
disjoinPredicates
    predicated1@Predicated
        { term = term1
        , predicate = predicate1
        , substitution = substitution1
        }
    predicated2@Predicated
        { term = term2
        , predicate = predicate2
        , substitution = substitution2
        }

  | term1         == term2
  =
    let result
          | substitution1 == substitution2 =
            predicated1 { predicate = makeOrPredicate predicate1 predicate2 }
\end{code}

When the configurations have different substitutions, it is possible to disjoin
them by promoting the substitutions into the predicate,
```
(t, p₁     , s₁) ∨ (t, p₂     , s₂)
(t, p₁ ∧ s₁, ⊤ ) ∨ (t, p₂ ∧ s₂, ⊤ )
```
and following the algorithm described above for disjoining predicates when the
substitutions are equal. This is not strictly a simplification: simplifying
predicates extracts substitutions into the corresponding field of the
configuration. Nevertheless, this simplification is required by
`Kore.Step.Simplification.Equals.makeEvaluateFunctionalOr`.

\begin{code}
          | otherwise =
            Predicated
                { term = term1
                , predicate =
                    Function.on
                        makeOrPredicate
                        Predicated.toPredicate
                        predicated1
                        predicated2
                , substitution = mempty
                }
    in Just (result, SimplificationProof)

  | otherwise =
    Nothing
\end{code}

== `\top` annihilates `\or`

\begin{code}
{- | 'Top' patterns are the annihilator of 'Or'.
 -}
topAnnihilates
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -- ^ Configuration
    -> ExpandedPattern level variable
    -- ^ Disjunction
    -> Maybe (ExpandedPattern level variable, SimplificationProof level)
\end{code}

`⊤` is the annihilator of `∨`; when two configurations have the same
substitution, it may be possible to use this property to simplify the pair by
annihilating the lesser term.
```
(⊤,              p₁, s) ∨ (t₂,              p₂, s)
(⊤, [p₂ ∨ ¬p₂] ∧ p₁, s) ∨ (t₂, [p₁ ∨ ¬p₁] ∧ p₂, s)

(⊤, p₁ ∧ p₂, s) ∨ (⊤, p₁ ∧ ¬p₂, s) ∨ (t₂, ¬p₁ ∧ p₂, s)
```
It is useful to apply the above equality when
```
¬p₂ ∧ p₁ = ¬p₁ ∧ p₂ = ⊥
p₁ = p₂
```
so that
```
(⊤, p₁, s) ∨ (t₂, p₂, s) = (⊤, p₁ ∧ p₂, s)
  where
    p₁ = p₂.
```

\begin{code}
topAnnihilates
    predicated1@Predicated
        { term = term1
        , predicate = predicate1
        , substitution = substitution1
        }
    predicated2@Predicated
        { term = term2
        , predicate = predicate2
        , substitution = substitution2
        }

  -- The 'term's are checked first because checking the equality of predicates
  -- and substitutions could be expensive.

  | _ :< TopPattern _ <- Recursive.project term1
  , predicate1    == predicate2
  , substitution1 == substitution2
  = Just (predicated1, SimplificationProof)

  | _ :< TopPattern _ <- Recursive.project term2
  , predicate1    == predicate2
  , substitution1 == substitution2
  = Just (predicated2, SimplificationProof)

  | otherwise =
    Nothing
\end{code}
