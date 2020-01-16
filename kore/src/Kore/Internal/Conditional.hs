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
    , splitTerm
    , isPredicate
    , Kore.Internal.Conditional.mapVariables
    , isNormalized
    ) where

import Control.Comonad
    ( Comonad (..)
    )
import Control.DeepSeq
    ( NFData
    )
import Data.Hashable
import Data.Monoid
    ( (<>)
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    , singleSubstitutionToPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( InternalVariable
    , Sort
    , TermLike
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as Internal
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

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
    ( Debug variable, Debug child, Diff variable, Diff child, Ord variable )
    => Diff (Conditional variable child)

instance
    (Hashable child, Hashable variable) =>
    Hashable (Conditional variable child)

instance
    (NFData child, NFData variable) =>
    NFData (Conditional variable child)

instance
    (InternalVariable variable, Semigroup term)
    => Semigroup (Conditional variable term)
  where
    (<>) predicated1 predicated2 = (<>) <$> predicated1 <*> predicated2
    {-# INLINE (<>) #-}

instance
    (InternalVariable variable, Monoid term)
    => Monoid (Conditional variable term)
  where
    mempty =
        Conditional
            { term = mempty
            , predicate = Predicate.makeTruePredicate_
            , substitution = mempty
            }
    {-# INLINE mempty #-}

    mappend = (<>)
    {-# INLINE mappend #-}

instance InternalVariable variable => Applicative (Conditional variable) where
    pure term =
        Conditional
            { term
            , predicate = Predicate.makeTruePredicate_
            , substitution = mempty
            }

    (<*>) predicated1 predicated2 =
        Conditional
            { term = f a
            , predicate = Predicate.makeAndPredicate predicate1 sortedPredicate2
            , substitution = substitution1 <> substitution2
            }
      where
        Conditional f predicate1 substitution1 = predicated1
        Conditional a predicate2 substitution2 = predicated2
        sort = Predicate.predicateSort predicate1
        sortedPredicate2 = Predicate.coerceSort sort predicate2

{- | 'Conditional' is equivalent to the 'Control.Comonad.Env.Env' comonad.

That is to say, @Conditional variable term@ is a @term@ together with its
environment (in this case, a conjunction of side conditions).

@extract@ returns the 'term' of the 'Conditional'.

@duplicate@ re-wraps the 'Conditional' with its own side conditions.

 -}
instance Comonad (Conditional variable) where
    extract = term
    {-# INLINE extract #-}

    duplicate conditional = conditional { term = conditional }
    {-# INLINE duplicate #-}

    extend f conditional = conditional { term = f conditional }
    {-# INLINE extend #-}

instance TopBottom term => TopBottom (Conditional variable term) where
    isTop Conditional {term, predicate, substitution} =
        isTop term && isTop predicate && isTop substitution
    isBottom Conditional {term, predicate, substitution} =
        isBottom term || isBottom predicate || isBottom substitution

unparseConditional
    :: Sort
    -> Doc ann    -- ^ term
    -> Doc ann    -- ^ predicate
    -> [Doc ann]  -- ^ substitution
    -> Doc ann
unparseConditional sort termDoc predicateDoc substitutionDocs =
    unparseAssoc' andHead andIdent
        [ below "/* term: */" termDoc
        , below "/* predicate: */" predicateDoc
        , below "/* substitution: */"
            (unparseAssoc' andHead andIdent substitutionDocs)
        ]
  where
    andHead = "\\and" <> parameters' [unparse sort]
    andIdent = "\\top" <> parameters' [unparse sort] <> noArguments
    below first second = (Pretty.align . Pretty.vsep) [first, second]

instance InternalVariable variable => Unparse (Conditional variable ()) where
    unparse conditional@Conditional { predicate } =
        unparse conditional { term = Internal.mkTop sort :: TermLike variable }
      where
        sort = termLikeSort termLikePredicate
        termLikePredicate = Predicate.unwrapPredicate predicate

    unparse2 conditional@Conditional { predicate } =
        unparse2 conditional { term = Internal.mkTop sort :: TermLike variable }
      where
        sort = termLikeSort termLikePredicate
        termLikePredicate = Predicate.unwrapPredicate predicate

instance
    InternalVariable variable
    => Unparse (Conditional variable (TermLike variable))
  where
    unparse Conditional { term, predicate, substitution } =
        unparseConditional
            sort
            (unparse term)
            (unparse termLikePredicate)
            (unparse <$> termLikeSubstitution)
      where
        sort = termLikeSort term
        termLikePredicate = Predicate.coerceSort sort predicate
        termLikeSubstitution =
            Predicate.coerceSort sort
            .  singleSubstitutionToPredicate
            <$> Substitution.unwrap substitution

    unparse2 Conditional { term, predicate, substitution } =
        unparseConditional
            sort
            (unparse2 term)
            (unparse2 termLikePredicate)
            (unparse2 <$> termLikeSubstitution)
      where
        sort = termLikeSort term
        termLikePredicate = Predicate.coerceSort sort predicate
        termLikeSubstitution =
            Predicate.coerceSort sort
            .  singleSubstitutionToPredicate
            <$> Substitution.unwrap substitution

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
    :: InternalVariable variable
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
    :: InternalVariable variable
    => Substitution variable
    -> Conditional variable ()
fromSubstitution substitution =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate_
        , substitution
        }

{- | Construct a 'Conditional' holding a single substitution.

The result has a true 'Predicate'.

 -}
fromSingleSubstitution
    :: InternalVariable variable
    => (UnifiedVariable variable, TermLike variable)
    -> Conditional variable ()
fromSingleSubstitution (variable, termLike) =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate_
        , substitution = Substitution.singleton variable termLike
        }

{- | Combine the predicate with the conditions of the first argument.
 -}
andPredicate
    :: InternalVariable variable
    => Conditional variable term
    -> Predicate variable
    -> Conditional variable term
andPredicate config predicate = config `andCondition` fromPredicate predicate

instance
    (Ord variable, HasFreeVariables term variable)
    => HasFreeVariables (Conditional variable term) variable
  where
    freeVariables Conditional { term, predicate, substitution } =
        freeVariables term
        <> freeVariables predicate
        <> freeVariables substitution

{- | Check if a Conditional can be reduced to a Predicate.
-}
isPredicate
    :: TopBottom term
    => Conditional variable term
    -> Bool
isPredicate Conditional {term} = isTop term

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
