{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Representation of conditional terms.
-}
module Kore.Internal.Conditional
    ( Conditional (..)
    , withoutTerm
    , withCondition
    , andCondition
    , fromPredicate
    , fromSubstitution
    , fromSingleSubstitution
    , andPredicate
    , Kore.Internal.Conditional.freeVariables
    , splitTerm
    , toPredicate
    , Kore.Internal.Conditional.mapVariables
    , isNormalized
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
import           Data.Monoid
                 ( (<>) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import           Kore.Attribute.Pattern.FreeVariables
                 ( FreeVariables )
import           Kore.Debug
import           Kore.Internal.TermLike
                 ( TermLike, termLikeSort )
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Syntax
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable )

{- | @Conditional@ represents a value conditioned on a predicate.

@Conditional variable child@ represents a @child@ conditioned on a
@predicate@ and @substitution@ (which is a specialized form of predicate).

The 'Applicative' instance conjoins the predicates and substitutions so that the
result is conditioned on the combined predicates of the inputs. The combined
predicate and substitution are /not/ normalized.

There is intentionally no 'Monad' instance; such an instance would have
quadratic complexity.

 -}
data Conditional variable child =
    Conditional
        { term :: child
        , predicate :: !(Predicate variable)
        , substitution :: !(Substitution variable)
        }
    deriving (Foldable, Functor, GHC.Generic, Traversable)

deriving instance
    (Eq child, Ord variable) =>
    Eq (Conditional variable child)

deriving instance
    (Ord child, Ord variable) =>
    Ord (Conditional variable child)

deriving instance
    (Show child, Show variable) =>
    Show (Conditional variable child)

instance SOP.Generic (Conditional variable child)

instance SOP.HasDatatypeInfo (Conditional variable child)

instance (Debug variable, Debug child) => Debug (Conditional variable child)

instance
    (Hashable child, Hashable variable) =>
    Hashable (Conditional variable child)

instance
    (NFData child, NFData variable) =>
    NFData (Conditional variable child)

instance
    ( Ord variable
    , Unparse variable
    , SortedVariable variable
    , Semigroup term
    ) =>
    Semigroup (Conditional variable term)
  where
    (<>) predicated1 predicated2 = (<>) <$> predicated1 <*> predicated2
    {-# INLINE (<>) #-}

instance
    ( Ord variable
    , Unparse variable
    , SortedVariable variable
    , Monoid term
    ) =>
    Monoid (Conditional variable term)
  where
    mempty =
        Conditional
            { term = mempty
            , predicate = Predicate.makeTruePredicate
            , substitution = mempty
            }
    {-# INLINE mempty #-}

    mappend = (<>)
    {-# INLINE mappend #-}

instance
    ( SortedVariable variable
    , Ord variable
    , Unparse variable
    ) =>
    Applicative (Conditional variable)
  where
    pure term =
        Conditional
            { term
            , predicate = Predicate.makeTruePredicate
            , substitution = mempty
            }

    (<*>) predicated1 predicated2 =
        Conditional
            { term = f a
            , predicate = Predicate.makeAndPredicate predicate1 predicate2
            , substitution = substitution1 <> substitution2
            }
      where
        Conditional f predicate1 substitution1 = predicated1
        Conditional a predicate2 substitution2 = predicated2

instance TopBottom term
    => TopBottom (Conditional variable term)
  where
    isTop Conditional {term, predicate, substitution} =
        isTop term && isTop predicate && isTop substitution
    isBottom Conditional {term, predicate, substitution} =
        isBottom term || isBottom predicate || isBottom substitution

instance ( SortedVariable variable
         , Ord variable
         , Show variable
         , Unparse variable
         ) => Unparse (Conditional variable (TermLike variable)) where
    unparse Conditional { term, predicate, substitution } =
        unparseAnd
            (below "/* term: */" (unparse term))
            (unparseAnd
                (below
                    "/* predicate: */"
                    (unparse termLikePredicate)
                )
                (below
                    "/* substitution: */"
                    (unparse termLikeSubstitution)
                )
            )
      where
        unparseAnd first second =
            "\\and" <> parameters' [unparse sort] <> arguments' [first, second]
        below first second =
            (Pretty.align . Pretty.vsep) [first, second]
        sort = termLikeSort term
        termLikePredicate = Predicate.fromPredicate sort predicate
        termLikeSubstitution =
            Predicate.fromPredicate
                sort
                $ Predicate.fromSubstitution substitution

    unparse2 Conditional { term, predicate, substitution } =
        unparseAnd2
            (below "/* term: */" (unparse2 term))
            (unparseAnd2
                (below
                    "/* predicate: */"
                    (unparse2 termLikePredicate)
                )
                (below
                    "/* substitution: */"
                    (unparse2 termLikeSubstitution)
                )
            )
      where
        unparseAnd2 first second =
            "\\and2" <> parameters' [unparse sort] <> arguments' [first, second]
        below first second =
            (Pretty.align . Pretty.vsep) [first, second]
        sort = termLikeSort term
        termLikePredicate = Predicate.fromPredicate sort predicate
        termLikeSubstitution =
            Predicate.fromPredicate
                sort
                $ Predicate.fromSubstitution substitution

{- | Forget the 'term', keeping only the attached conditions.
 -}
withoutTerm :: Conditional variable term -> Conditional variable ()
withoutTerm predicated = predicated { term = () }

{- | Attach the condition to the given 'term'.
 -}
withCondition
    :: term
    -> Conditional variable ()
    -- ^ Condition
    -> Conditional variable term
withCondition term predicated = predicated { term }

{- | Combine the conditions of both arguments, taking the 'term' of the first.
 -}
andCondition
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => Conditional variable term
    -> Conditional variable ()
    -> Conditional variable term
andCondition = (<*)

{- | Construct a 'Conditional' holding the given 'Predicate'.

The result has an empty 'Substitution'.

 -}
fromPredicate
    :: Ord variable
    => Predicate variable
    -> Conditional variable ()
fromPredicate predicate =
    Conditional { term = (), predicate, substitution = mempty }

{- | Construct a 'Conditional' holding the given 'Substitution'.

The result has a true 'Predicate'.

 -}
fromSubstitution
    :: (Ord variable, SortedVariable variable)
    => Substitution variable
    -> Conditional variable ()
fromSubstitution substitution =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution
        }

{- | Construct a 'Conditional' holding a single substitution.

The result has a true 'Predicate'.

 -}
fromSingleSubstitution
    :: (Ord variable, SortedVariable variable)
    => (UnifiedVariable variable, TermLike variable)
    -> Conditional variable ()
fromSingleSubstitution pair =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution = Substitution.wrap [pair]
        }

{- | Combine the predicate with the conditions of the first argument.
 -}
andPredicate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => Conditional variable term
    -> Predicate variable
    -> Conditional variable term
andPredicate config predicate = config `andCondition` fromPredicate predicate

{- | Extract the set of free variables from a 'Conditional' term.

See also: 'Predicate.freeVariables'.
-}
freeVariables
    :: Ord variable
    => (term -> FreeVariables variable)
    -- ^ Extract the free variables of @term@.
    -> Conditional variable term
    -> FreeVariables variable
freeVariables getFreeVariables Conditional { term, predicate, substitution } =
    getFreeVariables term
    <> Predicate.freeVariables predicate
    <> Substitution.freeVariables substitution

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'; i.e. when @term ~ ()@,

> Conditional variable term ~ Predicate variable

@toPredicate@ is also used to extract the 'Predicate' and 'Substitution' while
discarding the 'term'.

See also: 'substitutionToPredicate'.

-}
toPredicate
    :: ( SortedVariable variable
       , Ord variable
       , Show variable
       , Unparse variable
       )
    => Conditional variable term
    -> Predicate variable
toPredicate Conditional { predicate, substitution } =
    Predicate.makeAndPredicate
        predicate
        (Predicate.fromSubstitution substitution)

{- | Transform all variables (free and quantified) in a 'Conditional' term.

-}
mapVariables
    :: (Ord variableFrom, Ord variableTo)
    => ((variableFrom -> variableTo) -> termFrom -> termTo)
    -> (variableFrom -> variableTo)
    -> Conditional variableFrom termFrom
    -> Conditional variableTo   termTo
mapVariables
    mapTermVariables
    mapVariable
    Conditional { term, predicate, substitution }
  =
    Conditional
        { term = mapTermVariables mapVariable term
        , predicate = Predicate.mapVariables mapVariable predicate
        , substitution = Substitution.mapVariables mapVariable substitution
        }

splitTerm :: Conditional variable term -> (term, Conditional variable ())
splitTerm patt@Conditional { term } = (term, withoutTerm patt)

{- | Is the condition normalized?

The 'Substitution' must be normalized and must have been substituted into the
'Predicate'.

 -}
isNormalized :: Ord variable => Conditional variable term -> Bool
isNormalized Conditional { predicate, substitution } =
    Substitution.isNormalized substitution
    && Predicate.isFreeOf predicate (Substitution.variables substitution)
