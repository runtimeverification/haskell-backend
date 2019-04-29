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

import           Kore.AST.Common
                 ( Application, Pattern (..) )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject, Object, OrdMetaOrObject, ShowMetaOrObject )
import           Kore.AST.Pure
                 ( fromPurePattern )
import           Kore.AST.Valid
                 ( Valid )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( merge )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier )
import           Kore.Step.TermLike
                 ( TermLike )
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
newtype BuiltinAndAxiomSimplifier level =
    BuiltinAndAxiomSimplifier
        (forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , SortedVariable variable
            , Show (variable level)
            , Show (variable Object)
            , Unparse (variable level)
            , ShowMetaOrObject variable
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier level
        -> TermLikeSimplifier level
        -> BuiltinAndAxiomSimplifierMap level
        -> TermLike variable
        -> Simplifier
            ( AttemptedAxiom level variable
            , SimplificationProof level
            )
        )

{-|A type to abstract away the mapping from symbol identifiers to
their corresponding evaluators.
-}
type BuiltinAndAxiomSimplifierMap level =
    Map.Map (AxiomIdentifier level) (BuiltinAndAxiomSimplifier level)

{-| A type holding the result of applying an axiom to a pattern.
-}
data AttemptedAxiomResults level variable =
    AttemptedAxiomResults
        { results :: !(OrPattern level variable)
        -- ^ The result of applying the axiom
        , remainders :: !(OrPattern level variable)
        -- ^ The part of the pattern that was not rewritten by the axiom.
        }
    deriving Generic

deriving instance Eq (variable Object) => Eq (AttemptedAxiomResults level variable)
deriving instance Show (variable Object) => Show (AttemptedAxiomResults level variable)

instance (NFData (variable Object))
    => NFData (AttemptedAxiomResults level variable)

instance Ord (variable Object)
    => Semigroup (AttemptedAxiomResults level variable)
  where
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

instance
    Ord (variable Object) => Monoid (AttemptedAxiomResults Object variable)
  where
    mempty =
        AttemptedAxiomResults
            { results = OrPattern.bottom
            , remainders = OrPattern.bottom
            }

{-| 'AttemptedAxiom' holds the result of axiom-based simplification, with
a case for axioms that can't be applied.
-}
data AttemptedAxiom level variable
    = NotApplicable
    | Applied !(AttemptedAxiomResults level variable)
    deriving Generic

deriving instance Eq (variable Object) => Eq (AttemptedAxiom level variable)
deriving instance Show (variable Object) => Show (AttemptedAxiom level variable)

instance (NFData (variable Object))
    => NFData (AttemptedAxiom level variable)

{-| 'CommonAttemptedAxiom' particularizes 'AttemptedAxiom' to 'Variable',
following the same pattern as the other `Common*` types.
-}
type CommonAttemptedAxiom level = AttemptedAxiom level Variable

{- | Does the 'AttemptedAxiom' have remainders?

A 'NotApplicable' result is not considered to have remainders.

 -}
hasRemainders :: AttemptedAxiom level variable -> Bool
hasRemainders (Applied axiomResults) = (not . null) (remainders axiomResults)
hasRemainders NotApplicable = False

{- | Return a 'NotApplicable' result for a failing 'ExceptT' action.
 -}
exceptNotApplicable
    :: Functor m
    => ExceptT e m (AttemptedAxiom level variable, SimplificationProof level)
    ->           m (AttemptedAxiom level variable, SimplificationProof level)
exceptNotApplicable =
    fmap (either (const notApplicable) id) . runExceptT
  where
    notApplicable = (NotApplicable, SimplificationProof)

-- |Yields a pure 'Simplifier' which always returns 'NotApplicable'
notApplicableAxiomEvaluator
    :: Simplifier
        (AttemptedAxiom level1 variable, SimplificationProof level2)
notApplicableAxiomEvaluator = pure (NotApplicable, SimplificationProof)

-- |Yields a pure 'Simplifier' which produces a given 'TermLike'
purePatternAxiomEvaluator
    :: (MetaOrObject level, Ord (variable level))
    => TermLike variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
purePatternAxiomEvaluator p =
    pure
        ( Applied AttemptedAxiomResults
            { results = OrPattern.fromTermLike p
            , remainders = OrPattern.fromPatterns []
            }
        , SimplificationProof
        )

{-| Creates an 'BuiltinAndAxiomSimplifier' from a similar function that takes an
'Application'.
-}
applicationAxiomSimplifier
    :: forall level
    .   ( forall variable
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , OrdMetaOrObject variable
            , SortedVariable variable
            , Show (variable level)
            , Show (variable Object)
            , Unparse (variable level)
            , ShowMetaOrObject variable
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier level
        -> TermLikeSimplifier level
        -> BuiltinAndAxiomSimplifierMap level
        -> CofreeF
            (Application level)
            (Valid (variable level) level)
            (TermLike variable)
        -> Simplifier
            ( AttemptedAxiom level variable
            , SimplificationProof level
            )
        )
    -> BuiltinAndAxiomSimplifier level
applicationAxiomSimplifier applicationSimplifier =
    BuiltinAndAxiomSimplifier helper
  where
    helper
        ::  ( forall variable
            .   ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , OrdMetaOrObject variable
                , SortedVariable variable
                , Show (variable level)
                , Show (variable Object)
                , Unparse (variable level)
                , ShowMetaOrObject variable
                )
            => SmtMetadataTools StepperAttributes
            -> PredicateSimplifier level
            -> TermLikeSimplifier level
            -> BuiltinAndAxiomSimplifierMap level
            -> TermLike variable
            -> Simplifier
                ( AttemptedAxiom level variable
                , SimplificationProof level
                )
        )
    helper
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        patt
      =
        case fromPurePattern patt of
            (valid :< ApplicationPattern p) ->
                applicationSimplifier
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    (valid :< p)
            _ -> error
                ("Expected an application pattern, but got: " ++ show patt)
