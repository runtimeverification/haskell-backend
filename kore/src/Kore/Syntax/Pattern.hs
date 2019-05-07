{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Syntax.Pattern
    ( Pattern (..)
    , CommonPattern
    , ConcretePattern
    , VerifiedPattern
    , asPattern
    , fromPattern
    , eraseAnnotations
    , traverseVariables
    , mapVariables
    , asConcretePattern
    , isConcrete
    , fromConcretePattern
    , castVoidDomainValues
    -- * Re-exports
    , Base, CofreeF (..)
    , PatternF (..)
    , module Control.Comonad
    ) where

import           Control.Comonad
import           Control.Comonad.Trans.Cofree
                 ( Cofree, CofreeF (..), ComonadCofree (..) )
import qualified Control.Comonad.Trans.Env as Env
import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Bifunctor as Bifunctor
import           Data.Functor.Classes
import           Data.Functor.Compose
                 ( Compose (..) )
import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
                 ( Hashable (..) )
import           Data.Maybe
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
                 ( Pattern )
import           Kore.Syntax.Bottom
import           Kore.Syntax.PatternF
                 ( PatternF (..) )
import qualified Kore.Syntax.PatternF as PatternF
import           Kore.Syntax.Top
import           Kore.Syntax.Variable
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

{- | The abstract syntax of Kore at a fixed level @level@.

@dom@ is the type of domain values; see "Kore.Domain.External" and
"Kore.Domain.Builtin".

@var@ is the family of variable types, parameterized by level.

@ann@ is the type of annotations decorating each node of the abstract syntax
tree. @Pattern@ is a 'Traversable' 'Comonad' over the type of annotations.

-}
newtype Pattern
    (domain :: * -> *)
    (variable :: *)
    (annotation :: *)
  =
    Pattern
        { getPattern :: Cofree (PatternF domain variable) annotation }
    deriving (Foldable, Functor, Generic, Traversable)

instance
    ( Eq variable , Eq1 domain, Functor domain ) =>
    Eq (Pattern domain variable annotation)
  where
    (==) = eqWorker
      where
        eqWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            liftEq eqWorker pat1 pat2
    {-# INLINE (==) #-}

instance
    ( Ord variable , Ord1 domain, Functor domain ) =>
    Ord (Pattern domain variable annotation)
  where
    compare = compareWorker
      where
        compareWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            liftCompare compareWorker pat1 pat2
    {-# INLINE compare #-}

deriving instance
    ( Show annotation
    , Show variable
    , Show1 domain
    , child ~ Cofree (PatternF domain variable) annotation
    ) =>
    Show (Pattern domain variable annotation)

instance
    ( Functor domain
    , Hashable variable
    , Hashable (domain child)
    , child ~ Pattern domain variable annotation
    ) =>
    Hashable (Pattern domain variable annotation)
  where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance
    ( Functor domain
    , NFData annotation
    , NFData variable
    , NFData (domain child)
    , child ~ Pattern domain variable annotation
    ) =>
    NFData (Pattern domain variable annotation)
  where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat `seq` ()

instance
    ( Functor domain
    , Unparse variable
    , Unparse (domain self)
    , self ~ Pattern domain variable annotation
    ) =>
    Unparse (Pattern domain variable annotation)
  where
    unparse (Recursive.project -> _ :< pat) = unparse pat
    unparse2 (Recursive.project -> _ :< pat) = unparse2 pat


type instance Base (Pattern domain variable annotation) =
    CofreeF (PatternF domain variable) annotation

-- This instance implements all class functions for the Pattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Recursive (Pattern domain variable annotation)
  where
    project = \(Pattern embedded) ->
        case Recursive.project embedded of
            Compose (Identity projected) -> Pattern <$> projected
    {-# INLINE project #-}

    -- This specialization is particularly important: The default implementation
    -- of 'cata' in terms of 'project' would involve an extra call to 'fmap' at
    -- every level of the tree due to the implementation of 'project' above.
    cata alg = \(Pattern fixed) ->
        Recursive.cata
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE cata #-}

    para alg = \(Pattern fixed) ->
        Recursive.para
            (\(Compose (Identity base)) ->
                 alg (Bifunctor.first Pattern <$> base)
            )
            fixed
    {-# INLINE para #-}

    gpara dist alg = \(Pattern fixed) ->
        Recursive.gpara
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> alg (Env.local Pattern <$> base))
            fixed
    {-# INLINE gpara #-}

    prepro pre alg = \(Pattern fixed) ->
        Recursive.prepro
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE prepro #-}

    gprepro dist pre alg = \(Pattern fixed) ->
        Recursive.gprepro
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE gprepro #-}

-- This instance implements all class functions for the Pattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Corecursive (Pattern domain variable annotation)
  where
    embed = \projected ->
        (Pattern . Recursive.embed . Compose . Identity)
            (getPattern <$> projected)
    {-# INLINE embed #-}

    ana coalg = Pattern . ana0
      where
        ana0 =
            Recursive.ana (Compose . Identity . coalg)
    {-# INLINE ana #-}

    apo coalg = Pattern . apo0
      where
        apo0 =
            Recursive.apo
                (\a ->
                     (Compose . Identity)
                        (Bifunctor.first getPattern <$> coalg a)
                )
    {-# INLINE apo #-}

    postpro post coalg = Pattern . postpro0
      where
        postpro0 =
            Recursive.postpro
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE postpro #-}

    gpostpro dist post coalg = Pattern . gpostpro0
      where
        gpostpro0 =
            Recursive.gpostpro
                (Compose . Identity . dist . (<$>) (runIdentity . getCompose))
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE gpostpro #-}

-- This instance implements all class functions for the Pattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Comonad (Pattern domain variable)
  where
    extract = \(Pattern fixed) -> extract fixed
    {-# INLINE extract #-}
    duplicate = \(Pattern fixed) -> Pattern (extend Pattern fixed)
    {-# INLINE duplicate #-}
    extend extending = \(Pattern fixed) ->
        Pattern (extend (extending . Pattern) fixed)
    {-# INLINE extend #-}

instance
    Functor domain =>
    ComonadCofree
        (PatternF domain variable)
        (Pattern domain variable)
  where
    unwrap = \(Pattern fixed) -> Pattern <$> unwrap fixed
    {-# INLINE unwrap #-}

instance Functor domain
    => TopBottom (Pattern domain variable annotation)
  where
    isTop (Recursive.project -> _ :< TopF Top {}) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomF Bottom {}) = True
    isBottom _ = False

fromPattern
    :: Functor domain
    => Pattern domain variable annotation
    -> Base
        (Pattern domain variable annotation)
        (Pattern domain variable annotation)
fromPattern = Recursive.project

asPattern
    :: Functor domain
    => Base
        (Pattern domain variable annotation)
        (Pattern domain variable annotation)
    -> Pattern domain variable annotation
asPattern = Recursive.embed

-- | Erase the annotations from any 'Pattern'.
eraseAnnotations
    :: Functor domain
    => Pattern domain variable erased
    -> Pattern domain variable Attribute.Null
eraseAnnotations = (<$) Attribute.Null

-- | A pure pattern at level @level@ with variables in the common 'Variable'.
type CommonPattern domain = Pattern domain Variable Attribute.Null

-- | A concrete pure pattern (containing no variables) at level @level@.
type ConcretePattern domain =
    Pattern domain Concrete (Attribute.Pattern Concrete)

-- | A pure pattern which has been parsed and verified.
type VerifiedPattern domain =
    Pattern domain Variable (Attribute.Pattern Variable)

{- | Use the provided traversal to replace all variables in a 'Pattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2 domain annotation.
        (Monad m, Traversable domain)
    => (variable1 -> m variable2)
    -> Pattern domain variable1 annotation
    -> m (Pattern domain variable2 annotation)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker
        :: Base
            (Pattern domain variable1 annotation)
            (m (Pattern domain variable2 annotation))
        -> m (Pattern domain variable2 annotation)
    traverseVariablesWorker (a :< pat) =
        reannotate <$> (PatternF.traverseVariables traversing =<< sequence pat)
      where
        reannotate pat' = Recursive.embed (a :< pat')

{- | Use the provided mapping to replace all variables in a 'Pattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

See also: 'traverseVariables'

 -}
mapVariables
    :: Functor domain
    => (variable1 -> variable2)
    -> Pattern domain variable1 annotation
    -> Pattern domain variable2 annotation
mapVariables mapping =
    Recursive.ana (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (a :< pat) =
        a :< PatternF.mapVariables mapping pat

-- | Use the provided mapping to replace all domain values in a 'Pattern'.
mapDomainValues
    ::  forall domain1 domain2 variable annotation.
        (Functor domain1, Functor domain2)
    => (forall child. domain1 child -> domain2 child)
    -> Pattern domain1 variable annotation
    -> Pattern domain2 variable annotation
mapDomainValues mapping =
    -- Using 'Recursive.unfold' so that the pattern will unfold lazily.
    -- Lazy unfolding allows composing multiple tree transformations without
    -- allocating the entire intermediates.
    Recursive.unfold (mapDomainValuesWorker . Recursive.project)
  where
    mapDomainValuesWorker (a :< pat) =
        a :< PatternF.mapDomainValues mapping pat

{- | Construct a 'ConcretePattern' from a 'Pattern'.

A concrete pattern contains no variables, so @asConcretePattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcretePattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcretePattern
    :: forall domain variable annotation . Traversable domain
    => Pattern domain variable annotation
    -> Maybe (Pattern domain Concrete annotation)
asConcretePattern = traverseVariables (\case { _ -> Nothing })

isConcrete
    :: forall domain variable annotation . Traversable domain
    => Pattern domain variable annotation
    -> Bool
isConcrete = isJust . asConcretePattern

{- | Construct a 'Pattern' from a 'ConcretePattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcretePattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcretePattern
    :: forall domain variable annotation. Functor domain
    => Pattern domain Concrete annotation
    -> Pattern domain variable annotation
fromConcretePattern = mapVariables (\case {})

{- | Cast a pure pattern with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: Functor domain
    => Pattern (Const Void) variable annotation
    -> Pattern domain variable annotation
castVoidDomainValues = mapDomainValues (\case {})
