{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Representation of program configurations as conditional patterns.
-}
module Kore.Internal.Pattern
    ( Pattern
    , fromPredicate
    , toPredicate
    , Kore.Internal.Pattern.allVariables
    , bottom
    , bottomOf
    , isBottom
    , isTop
    , Kore.Internal.Pattern.mapVariables
    , toTermLike
    , top
    , topOf
    , fromTermLike
    , Kore.Internal.Pattern.freeVariables
    -- * Re-exports
    , Conditional (..)
    , Conditional.withCondition
    , Conditional.withoutTerm
    , Predicate
    ) where

import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Predicate
                 ( Predicate )
import           Kore.Internal.TermLike as TermLike
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.TopBottom
                 ( TopBottom (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Free
                 ( pureAllVariables )

{- | The conjunction of a pattern, predicate, and substitution.

The form of @Pattern@ is intended to be a convenient representation of a
program configuration for Kore execution.

 -}
type Pattern variable = Conditional variable (TermLike variable)

fromPredicate :: Predicate variable -> Pattern variable
fromPredicate = (<$) mkTop_

freeVariables
    :: Ord variable
    => Pattern variable
    -> Set variable
freeVariables = Conditional.freeVariables TermLike.freeVariables

{-|'mapVariables' transforms all variables, including the quantified ones,
in an Pattern.
-}
mapVariables
    :: (Ord variableFrom, Ord variableTo)
    => (variableFrom -> variableTo)
    -> Pattern variableFrom
    -> Pattern variableTo
mapVariables
    variableMapper
    Conditional { term, predicate, substitution }
  =
    Conditional
        { term = TermLike.mapVariables variableMapper term
        , predicate = Syntax.Predicate.mapVariables variableMapper predicate
        , substitution =
            Substitution.mapVariables variableMapper substitution
        }

{-|'allVariables' extracts all variables, including the quantified ones,
from an Pattern.
-}
allVariables
    :: (Ord variable, Unparse variable)
    => Pattern variable
    -> Set.Set variable
allVariables
    Conditional { term, predicate, substitution }
  =
    pureAllVariables term
    <> Syntax.Predicate.allVariables predicate
    <> allSubstitutionVars (Substitution.unwrap substitution)
  where
    allSubstitutionVars sub =
        foldl
            (\ x y -> x <> Set.singleton (fst y))
            Set.empty
            sub
        <> foldl
            (\ x y -> x <> pureAllVariables (snd y))
            Set.empty
            sub

{- | Convert an 'Pattern' to an ordinary 'TermLike'.

Conversion relies on the interpretation of 'Pattern' as a conjunction of
patterns. Conversion erases the distinction between terms, predicates, and
substitutions; this function should be used with care where that distinction is
important.

 -}
toTermLike
    ::  forall variable.
        ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , HasCallStack
        )
    => Pattern variable -> TermLike variable
toTermLike Conditional { term, predicate, substitution } =
    simpleAnd
        (simpleAnd term predicate)
        (Syntax.Predicate.fromSubstitution substitution)
  where
    -- TODO: Most likely I defined this somewhere.
    simpleAnd
        :: TermLike variable
        -> Syntax.Predicate variable
        -> TermLike variable
    simpleAnd pattern' predicate'
      | isTop predicate'    = pattern'
      | isBottom predicate' = mkBottom sort
      | isTop pattern'      = predicateTermLike
      | isBottom pattern'   = pattern'
      | otherwise           = mkAnd pattern' predicateTermLike
      where
        predicateTermLike = Syntax.Predicate.fromPredicate sort predicate'
        sort = termLikeSort pattern'

{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: Ord variable => Pattern variable
bottom =
    Conditional
        { term      = mkBottom_
        , predicate = Syntax.Predicate.makeFalsePredicate
        , substitution = mempty
        }

{- | An 'Pattern' where the 'term' is 'Bottom' of the given 'Sort'.

The 'predicate' is set to 'makeFalsePredicate'.

 -}
bottomOf :: Ord variable => Sort -> Pattern variable
bottomOf resultSort =
    Conditional
        { term      = mkBottom resultSort
        , predicate = Syntax.Predicate.makeFalsePredicate
        , substitution = mempty
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: Ord variable => Pattern variable
top =
    Conditional
        { term      = mkTop_
        , predicate = Syntax.Predicate.makeTruePredicate
        , substitution = mempty
        }

{- | An 'Pattern' where the 'term' is 'Top' of the given 'Sort'.
 -}
topOf :: Ord variable => Sort -> Pattern variable
topOf resultSort =
    Conditional
        { term      = mkTop resultSort
        , predicate = Syntax.Predicate.makeTruePredicate
        , substitution = mempty
        }

{- | Construct an 'Pattern' from a 'TermLike'.

The resulting @Pattern@ has a true predicate and an empty
substitution, unless it is trivially 'Bottom'.

See also: 'makeTruePredicate', 'pure'

 -}
fromTermLike
    :: Ord variable
    => TermLike variable
    -> Pattern variable
fromTermLike term
  | isBottom term = bottom
  | otherwise =
    Conditional
        { term
        , predicate = Syntax.Predicate.makeTruePredicate
        , substitution = mempty
        }

toPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> Syntax.Predicate variable
toPredicate = Conditional.toPredicate
