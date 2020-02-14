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
    , markPredicateSimplified
    , markPredicateSimplifiedConditional
    , setPredicateSimplified
    ) where

import Prelude.Kore

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
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.Simplified as Attribute
    ( Simplified
    )
import Kore.Debug
import Kore.Internal.Predicate
    ( Predicate
    , singleSubstitutionToPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.Substitution
    ( Assignment
    , pattern Assignment_
    , Substitution
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
import Kore.Variables.Fresh
    ( FreshVariable
    )
import Kore.Variables.UnifiedVariable
    ( ElementVariable
    , SetVariable
    , UnifiedVariable
    )
import qualified SQL

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
    (Eq child, InternalVariable variable) =>
    Eq (Conditional variable child)

deriving instance
    (Ord child, InternalVariable variable) =>
    Ord (Conditional variable child)

deriving instance
    (Show child, Show variable) =>
    Show (Conditional variable child)

instance SOP.Generic (Conditional variable child)

instance SOP.HasDatatypeInfo (Conditional variable child)

instance (Debug variable, Debug child) => Debug (Conditional variable child)

instance
    ( Debug variable, Debug child, Diff variable, Diff child, InternalVariable variable )
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

instance
    InternalVariable variable
    => From (Conditional variable ()) (Predicate variable)
  where
    from Conditional { predicate, substitution } =
        Predicate.makeAndPredicate predicate (from substitution)

instance
    InternalVariable variable
    => From (Predicate variable) (Conditional variable ())
  where
    from predicate =
        Conditional { term = (), predicate, substitution = mempty }

instance
    InternalVariable variable
    => From (Substitution variable) (Conditional variable ())
  where
    from substitution =
        Conditional
            { term = ()
            , predicate = Predicate.makeTruePredicate_
            , substitution
            }

instance
    InternalVariable variable
    => From (Assignment variable) (Conditional variable ())
  where
    from = from @(Substitution variable) . from . Substitution.assignmentToPair

instance
    From from to
    => From (Conditional variable from) (Conditional variable to)
  where
    from = fmap from

instance
    InternalVariable variable
    => From term (Conditional variable term)
  where
    from = pure

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
            . singleSubstitutionToPredicate
            . Substitution.assignmentToPair
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
            . singleSubstitutionToPredicate
            . Substitution.assignmentToPair
            <$> Substitution.unwrap substitution

instance
    ( InternalVariable variable, Typeable variable
    , SQL.Column term, Typeable term
    )
    => SQL.Table (Conditional variable term)

instance
    ( InternalVariable variable, Typeable variable
    , SQL.Column term, Typeable term
    )
    => SQL.Column (Conditional variable term)
  where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

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
    :: InternalVariable variable
    => Predicate variable
    -> Conditional variable ()
fromPredicate = from

{- | Construct a 'Conditional' holding the given 'Substitution'.

The result has a true 'Predicate'.

 -}
fromSubstitution
    :: InternalVariable variable
    => Substitution variable
    -> Conditional variable ()
fromSubstitution = from

{- | Construct a 'Conditional' holding a single substitution.

The result has a true 'Predicate'.

 -}
fromSingleSubstitution
    :: InternalVariable variable
    => Assignment variable
    -> Conditional variable ()
fromSingleSubstitution = from

{- | Combine the predicate with the conditions of the first argument.
 -}
andPredicate
    :: InternalVariable variable
    => Conditional variable term
    -> Predicate variable
    -> Conditional variable term
andPredicate config predicate = config `andCondition` fromPredicate predicate

instance
    (InternalVariable variable, HasFreeVariables term variable)
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
    :: InternalVariable variableFrom
    => InternalVariable variableTo
    => FreshVariable variableTo
    => ((ElementVariable variableFrom -> ElementVariable variableTo) -> (SetVariable variableFrom -> SetVariable variableTo) -> termFrom -> termTo)
    -> (ElementVariable variableFrom -> ElementVariable variableTo)
    -> (SetVariable variableFrom -> SetVariable variableTo)
    -> Conditional variableFrom termFrom
    -> Conditional variableTo   termTo
mapVariables
    mapTermVariables
    mapElemVar
    mapSetVar
    Conditional { term, predicate, substitution }
  =
    Conditional
        { term = mapTermVariables mapElemVar mapSetVar term
        , predicate = Predicate.mapVariables mapElemVar mapSetVar predicate
        , substitution =
            Substitution.mapVariables mapElemVar mapSetVar substitution
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

{-| Marks the condition's predicate as being simplified.

Since the substitution is usually simplified, this usually marks the entire
condition as simplified. Note however, that the way in which the condition
is simplified is a combination of the predicate and substitution
simplifications. As an example, if the predicate is fully simplified,
while the substitution is simplified only for a certain side condition,
the entire condition is simplified only for that side condition.
-}
markPredicateSimplified
    :: (HasCallStack, InternalVariable variable)
    => Conditional variable term -> Conditional variable term
markPredicateSimplified conditional@Conditional { predicate } =
    conditional { predicate = Predicate.markSimplified predicate }

markPredicateSimplifiedConditional
    :: (HasCallStack, InternalVariable variable)
    => SideCondition.Representation
    -> Conditional variable term
    -> Conditional variable term
markPredicateSimplifiedConditional
    sideCondition
    conditional@Conditional { predicate }
  =
    conditional
        { predicate =
            Predicate.markSimplifiedConditional sideCondition predicate
        }

{-| Sets the simplified attribute for a condition's predicate.

See 'markPredicateSimplified' for details.
-}
setPredicateSimplified
    :: (InternalVariable variable)
    => Attribute.Simplified
    -> Conditional variable term
    -> Conditional variable term
setPredicateSimplified simplified conditional@Conditional { predicate } =
    conditional { predicate = Predicate.setSimplified simplified predicate }
