{-|
Module      : Kore.Step.ExpandedPattern
Description : Data structures and functions for manipulating
              ExpandedPatterns, i.e. a representation of patterns
              optimized for the stepper.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.ExpandedPattern
    ( Predicated (..)
    , ExpandedPattern
    , CommonExpandedPattern
    , PredicateSubstitution
    , CommonPredicateSubstitution
    , allVariables
    , erasePredicatedTerm
    , bottom
    , isBottom
    , isTop
    , mapVariables
    , substitutionToPredicate
    , toMLPattern
    , top
    , topPredicate
    , bottomPredicate
    , fromPurePattern
    , toPredicate
    , freeVariables
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Functor
                 ( ($>) )
import           Data.Monoid
                 ( (<>) )
import           Data.Reflection
                 ( Given )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Common
                 ( SortedVariable, Variable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( mapPatternVariables )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( Predicate, pattern PredicateFalse, pattern PredicateTrue,
                 makeAndPredicate, makeFalsePredicate, makeTruePredicate,
                 substitutionToPredicate, unwrapPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Pattern
import           Kore.Unification.Data
import           Kore.Variables.Free
                 ( pureAllVariables )

{- | @Predicated@ represents a value conditioned on a predicate.

@Predicated level variable child@ represents a @child@ conditioned on a
@predicate@ and @substitution@ (which is a specialized form of predicate).

The 'Applicative' instance conjoins the predicates and substitutions so that the
result is conditioned on the combined predicates of the inputs. The combined
predicate and substitution are /not/ normalized.

There is intentionally no 'Monad' instance; such an instance would have
quadratic complexity.

 -}
data Predicated level variable child = Predicated
    { term :: child
    , predicate :: !(Predicate level variable)
    , substitution :: !(UnificationSubstitution level variable)
    }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance
    (NFData child, NFData (variable level)) =>
    NFData (Predicated level variable child)

instance
    ( MetaOrObject level
    , SortedVariable variable
    , Show (variable level)
    , Eq (variable level)
    , Given (SymbolOrAliasSorts level)
    ) =>
    Applicative (Predicated level variable)
  where
    pure a = Predicated a makeTruePredicate []
    a <*> b =
        Predicated
            { term = f x
            , predicate = predicate1 `makeAndPredicate` predicate2
            , substitution = substitution1 ++ substitution2
            }
      where
        Predicated f predicate1 substitution1 = a
        Predicated x predicate2 substitution2 = b

{- | The conjunction of a pattern, predicate, and substitution.

The form of @ExpandedPattern@ is intended to be convenient for Kore execution.

 -}
type ExpandedPattern level variable =
    Predicated level variable (StepPattern level variable)

{- | 'CommonExpandedPattern' particularizes 'ExpandedPattern' to 'Variable'.
-}
type CommonExpandedPattern level = ExpandedPattern level Variable

-- | A predicate and substitution without an accompanying term.
type PredicateSubstitution level variable = Predicated level variable ()

-- | A 'PredicateSubstitution' of the 'Variable' type.
type CommonPredicateSubstitution level = PredicateSubstitution level Variable

{-|'mapVariables' transforms all variables, including the quantified ones,
in an ExpandedPattern.
-}
mapVariables
    :: (variableFrom level -> variableTo level)
    -> ExpandedPattern level variableFrom
    -> ExpandedPattern level variableTo
mapVariables
    variableMapper
    Predicated { term, predicate, substitution }
  =
    Predicated
        { term = mapPatternVariables variableMapper term
        , predicate = Predicate.mapVariables variableMapper predicate
        , substitution = mapSubstitutionVariables variableMapper substitution
        }

{-|'allVariables' extracts all variables, including the quantified ones,
from an ExpandedPattern.
-}
allVariables
    ::  Ord (variable level)
    => ExpandedPattern level variable
    -> Set.Set (variable level)
allVariables
    Predicated { term, predicate, substitution }
  =
    pureAllVariables term
    <> Predicate.allVariables predicate
    <> allSubstitutionVars substitution
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

-- | Erase the @Predicated@ 'term' to yield a 'PredicateSubstitution'.
erasePredicatedTerm
    :: Predicated level variable child
    -> PredicateSubstitution level variable
erasePredicatedTerm = (<$) ()

{-|'toMLPattern' converts an ExpandedPattern to a StepPattern.
-}
toMLPattern
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level))
    => ExpandedPattern level variable -> StepPattern level variable
toMLPattern
    Predicated { term, predicate, substitution }
  =
    simpleAnd
        (simpleAnd term predicate)
        (substitutionToPredicate substitution)
  where
    -- TODO: Most likely I defined this somewhere.
    simpleAnd
        ::  ( MetaOrObject level
            , Given (SymbolOrAliasSorts level)
            , SortedVariable variable
            , Show (variable level))
        => StepPattern level variable
        -> Predicate level variable
        -> StepPattern level variable
    simpleAnd (Top_ _)      predicate'     = unwrapPredicate predicate'
    simpleAnd patt          PredicateTrue  = patt
    simpleAnd b@(Bottom_ _) _              = b
    simpleAnd _             PredicateFalse = mkBottom
    simpleAnd pattern1      predicate'     =
        mkAnd pattern1 (unwrapPredicate predicate')

{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: MetaOrObject level => ExpandedPattern level variable
bottom =
    Predicated
        { term      = mkBottom
        , predicate = makeFalsePredicate
        , substitution = []
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: MetaOrObject level => ExpandedPattern level variable
top =
    Predicated
        { term      = mkTop
        , predicate = makeTruePredicate
        , substitution = []
        }

{-| 'isTop' checks whether an ExpandedPattern is equivalent to a top Pattern.
-}
isTop :: ExpandedPattern level variable -> Bool
isTop
    Predicated
        { term = Top_ _, predicate = PredicateTrue, substitution = [] }
  = True
isTop _ = False

{-| 'isBottom' checks whether an ExpandedPattern is equivalent to a bottom
Pattern.
-}
isBottom :: ExpandedPattern level variable -> Bool
isBottom
    Predicated {term = Bottom_ _}
  = True
isBottom
    Predicated {predicate = PredicateFalse}
  = True
isBottom _ = False

{- | Construct an 'ExpandedPattern' from a 'StepPattern'.

  The resulting @ExpandedPattern@ has a true predicate and an empty
  substitution.

  See also: 'makeTruePredicate', 'pure'

 -}
fromPurePattern
    :: MetaOrObject level
    => StepPattern level variable
    -> ExpandedPattern level variable
fromPurePattern term =
    case term of
        Bottom_ _ -> bottom
        _ ->
            Predicated
                { term
                , predicate = makeTruePredicate
                , substitution = []
                }

topPredicate :: MetaOrObject level => PredicateSubstitution level variable
topPredicate = top $> ()

bottomPredicate :: MetaOrObject level => PredicateSubstitution level variable
bottomPredicate = bottom $> ()

{- | Transform a predicate and substitution into a predicate only.

    See also: 'substitutionToPredicate'.

-}
toPredicate
    :: ( MetaOrObject level
       , Given (SymbolOrAliasSorts level)
       , SortedVariable variable
       , Eq (variable level)
       , Show (variable level)
       )
    => PredicateSubstitution level variable
    -> Predicate level variable
toPredicate Predicated { predicate, substitution } =
    makeAndPredicate
        predicate
        (substitutionToPredicate substitution)

{- | Extract the set of free variables from a predicate and substitution.

    See also: 'Predicate.freeVariables'.
-}

freeVariables
    :: ( MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , Given (SymbolOrAliasSorts level)
       , SortedVariable variable
       )
    => PredicateSubstitution level variable
    -> Set.Set (variable level)
freeVariables = Predicate.freeVariables . toPredicate
