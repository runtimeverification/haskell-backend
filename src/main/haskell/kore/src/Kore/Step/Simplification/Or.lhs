\ifheader
\section{Header}
\label{sec:or-header}

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
import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( makeOrPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, merge )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

\end{code}
\fi

\section{Driver}
\label{sec:or-driver}

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

\noindent
\lstinline!simplify! is a driver
responsible for breaking down an $\slor$ pattern and simplifying its children.

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

\textbf{TODO} (virgil): Preserve pattern sorts under simplification.

\noindent
One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type
\begin{lstlisting}
CofreeF (Or level) (Valid level) (OrOfExpandedPattern level variable)
\end{lstlisting}
instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

\textbf{TODO} (virgil): This should do all possible mergings, not just the first
term with the second.

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

\section{Disjoin predicates}
\label{sec:or-disjoin-predicates}

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

When two configurations have the same substitution,
it may be possible to simplify the pair by disjunction of their predicates.
\begin{dgroup*}
\begin{dmath*}
(t_1, p_1, s) \vee (t_2, p_2, s)
  =
([t_2 \vee \neg t_2] \wedge t_1, p_1, s)
  \vee
([t_1 \vee \neg t_1] \wedge t_2, p_2, s)
\end{dmath*}
\begin{dmath*}
{}
  =
(t_1 \wedge t_2, p_1 \vee p_2, s)
  \vee
(\neg t_2 \wedge t_1, p_1, s)
  \vee
(\neg t_1 \wedge t_2, p_2, s)
\end{dmath*}
\end{dgroup*}
It is useful to apply the above equality when
\(
\neg t_2 \wedge t_1
=
\neg t_1 \wedge t_2
=
\bot
\),
so that
\begin{dmath}
\label{eq:or-disjoin-predicates}
(t_1, p_1, s) \vee (t_2, p_2, s)
  =
(t_1 \wedge t_2, p_1 \vee p_2, s)
\condition{
  \(
  \neg t_2 \wedge t_1
    =
  \neg t_1 \wedge t_2
    =
  \bot
  \)
}
\end{dmath}.
Checking the side condition of Eq.~\eqref{eq:or-disjoin-predicates} may be
expensive, so in practice we only apply this simplification when
\(
t_1 = t_2
\).

Note: It is not clear that we should \emph{ever} apply this simplification.
We attempt to refute the conditions on configurations using an external solver
to reduce the configuration space for execution.
The solver operates best when it has the most information, and the predicate
\(
p_1 \vee p_2
\)
is strictly weaker than either $p_1$ or $p_2$.

\begin{code}
disjoinPredicates
    predicated1@Predicated
        { term = term1
        , predicate = predicate1
        , substitution = substitution1
        }
    Predicated
        { term = term2
        , predicate = predicate2
        , substitution = substitution2
        }

  | term1         == term2
  , substitution1 == substitution2
  = Just (result, SimplificationProof)

  | otherwise =
    Nothing

  where
    result = predicated1 { predicate = makeOrPredicate predicate1 predicate2 }

\end{code}

\section{\sltop~annihilates~\slor}
\label{sec:or-top-annihilates}

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

$\top$ is the annihilator of $\vee$;
when two configurations have the same substitution,
it may be possible to use this property to simplify the pair
by annihilating the lesser term.

\begin{dgroup*}
\begin{dmath*}
(\top, p_1, s) \vee (t_2, p_2, s)
  =
(\top, [p_2 \vee \neg p_2] \wedge p_1, s)
  \vee
(t_2, [p_1 \vee \neg p_1] \wedge p_2, s)
  =
(\top, p_1 \wedge p_2, s)
  \vee
(\top, p_1 \wedge \neg p_2, s)
  \vee
(t_2, \neg p_1 \wedge p_2, s)
\end{dmath*}
\end{dgroup*}
It is useful to apply the above equality when
\(
\neg p_2 \wedge p_1
=
\neg p_1 \wedge p_2
=
\bot
\),
so that
\begin{dmath}
\label{eq:or-top-annihilates}
(\top, p_1, s) \vee (t_2, p_2, s)
  =
(\top, p_1 \wedge p_2, s)
\condition{
  \(
  \neg p_2 \wedge p_1
    =
  \neg p_1 \wedge p_2
    =
  \bot
  \)
}
\end{dmath}.
Checking the side condition of Eq.~\eqref{eq:or-top-annihilates} may be
expensive, so in practice we only apply this simplification when
\(
p_1 = p_2
\).

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
