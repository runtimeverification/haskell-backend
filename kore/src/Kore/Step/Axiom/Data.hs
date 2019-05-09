{-|
Module      : Kore.Step.Axiom.Data
Description : Data structures used for axiom-based evaluation.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.Data
    ( BuiltinAndAxiomSimplifier (..)
    , BuiltinAndAxiomSimplifierMap
    , AttemptedAxiom (..)
    , AttemptedAxiomResults (..)
    , CommonAttemptedAxiom
    , hasRemainders
    , exceptNotApplicable
    , applicationAxiomSimplifier
    , notApplicableAxiomEvaluator
    , purePatternAxiomEvaluator
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Control.DeepSeq
                 ( NFData )
import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import qualified Data.Map.Strict as Map
import           GHC.Generics
                 ( Generic )

import qualified Kore.Attribute.Pattern as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( merge )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike
                 ( TermLike )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Syntax.Application
import           Kore.Syntax.Pattern
                 ( fromPattern )
import           Kore.Syntax.PatternF
                 ( PatternF (..) )
import           Kore.Syntax.Variable
                 ( SortedVariable, Variable (..) )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| 'BuiltinAndAxiomSimplifier' simplifies patterns using either an axiom
or builtin code.

Arguments:

* 'MetadataTools' are tools for finding additional information about
patterns such as their sorts, whether they are constructors or hooked.

* 'TermLikeSimplifier' is a Function for simplifying patterns, used for
the post-processing of the function application results.

* BuiltinAndAxiomSimplifierMap is a map from pattern identifiers to the
'BuiltinAndAxiomSimplifier's that handle those patterns.

* 'TermLike' is the pattern to be evaluated.

Return value:

It returns the result of simplifying the pattern with builtins and
axioms, together with a proof certifying that it was simplified correctly
(which is only a placeholder right now).
-}
newtype BuiltinAndAxiomSimplifier =
    BuiltinAndAxiomSimplifier
        (forall variable
        .   ( FreshVariable variable
            , SortedVariable variable
            , Show variable
            , Unparse variable
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Simplifier (AttemptedAxiom variable)
        )

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap =
    Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier

{-| A type holding the result of applying an axiom to a pattern.
-}
data AttemptedAxiomResults variable =
    AttemptedAxiomResults
        { results :: !(OrPattern variable)
        -- ^ The result of applying the axiom
        , remainders :: !(OrPattern variable)
        -- ^ The part of the pattern that was not rewritten by the axiom.
        }
    deriving Generic

deriving instance Ord variable => Eq (AttemptedAxiomResults variable)
deriving instance Show variable => Show (AttemptedAxiomResults variable)

instance (NFData variable) => NFData (AttemptedAxiomResults variable)

instance Ord variable => Semigroup (AttemptedAxiomResults variable) where
    (<>)
        AttemptedAxiomResults
            { results = firstResults
            , remainders = firstRemainders
            }
        AttemptedAxiomResults
            { results = secondResults
            , remainders = secondRemainders
            }
      =
        AttemptedAxiomResults
            { results = MultiOr.merge firstResults secondResults
            , remainders =
                    MultiOr.merge firstRemainders secondRemainders
            }

instance Ord variable => Monoid (AttemptedAxiomResults variable) where
    mempty =
        AttemptedAxiomResults
            { results = OrPattern.bottom
            , remainders = OrPattern.bottom
            }

{-| 'AttemptedAxiom' holds the result of axiom-based simplification, with
a case for axioms that can't be applied.
-}
data AttemptedAxiom variable
    = NotApplicable
    | Applied !(AttemptedAxiomResults variable)
    deriving Generic

deriving instance Ord variable => Eq (AttemptedAxiom variable)
deriving instance Show variable => Show (AttemptedAxiom variable)

instance (NFData variable) => NFData (AttemptedAxiom variable)

{-| 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom = AttemptedAxiom Variable

{- | Does the 'AttemptedAxiom' have remainders?

A 'NotApplicable' result is not considered to have remainders.

 -}
hasRemainders :: AttemptedAxiom variable -> Bool
hasRemainders (Applied axiomResults) = (not . null) (remainders axiomResults)
hasRemainders NotApplicable = False

{- | Return a 'NotApplicable' result for a failing 'ExceptT' action.
 -}
exceptNotApplicable
    :: Functor m
    => ExceptT e m (AttemptedAxiom variable)
    ->           m (AttemptedAxiom variable)
exceptNotApplicable =
    fmap (either (const notApplicable) id) . runExceptT
  where
    notApplicable = NotApplicable

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableAxiomEvaluator :: Simplifier (AttemptedAxiom variable)
notApplicableAxiomEvaluator = pure NotApplicable

-- |Yields a pure 'Simplifier' which produces a given 'TermLike'
purePatternAxiomEvaluator
    :: Ord variable
    => TermLike variable
    -> Simplifier (AttemptedAxiom variable)
purePatternAxiomEvaluator p =
    pure
        ( Applied AttemptedAxiomResults
            { results = OrPattern.fromTermLike p
            , remainders = OrPattern.fromPatterns []
            }

        )

{-| Creates an 'BuiltinAndAxiomSimplifier' from a similar function that takes an
'Application'.
-}
applicationAxiomSimplifier
    ::  ( forall variable
        .   ( FreshVariable variable
            , Ord variable
            , SortedVariable variable
            , Show variable
            , Show variable
            , Unparse variable
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> CofreeF
            (Application SymbolOrAlias)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> Simplifier (AttemptedAxiom variable)
        )
    -> BuiltinAndAxiomSimplifier
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper
        ::  ( forall variable
            .   ( FreshVariable variable
                , Ord variable
                , SortedVariable variable
                , Show variable
                , Show variable
                , Unparse variable
                )
            => SmtMetadataTools StepperAttributes
            -> PredicateSimplifier
            -> TermLikeSimplifier
            -> BuiltinAndAxiomSimplifierMap
            -> TermLike variable
            -> Simplifier (AttemptedAxiom variable)
        )
    helper
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        patt
      =
        case fromPattern patt of
            (valid :< ApplicationF p) ->
                applicationSimplifier
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show patt)
