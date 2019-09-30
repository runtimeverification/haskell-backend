{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Syntax.Pattern
    ( Pattern (..)
    , asPattern
    , fromPattern
    , eraseAnnotations
    , traverseVariables
    , mapVariables
    , asConcretePattern
    , isConcrete
    , fromConcretePattern
    -- * Re-exports
    , Base, CofreeF (..)
    , PatternF (..)
    , Const (..)
    , module Control.Comonad
    ) where

import Control.Comonad
import Control.Comonad.Trans.Cofree
    ( Cofree
    , CofreeF (..)
    , ComonadCofree (..)
    )
import qualified Control.Comonad.Trans.Env as Env
import Control.DeepSeq
    ( NFData (..)
    )
import qualified Data.Bifunctor as Bifunctor
import Data.Functor.Compose
    ( Compose (..)
    )
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity
    ( Identity (..)
    )
import Data.Hashable
    ( Hashable (..)
    )
import Data.Maybe
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Null as Attribute
import Kore.Debug
import Kore.Syntax.PatternF
    ( Const (..)
    , PatternF (..)
    )
import qualified Kore.Syntax.PatternF as PatternF
import Kore.Syntax.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser

{- | The abstract syntax of Kore.

@variable@ is the family of variable types.

@annotation@ is the type of annotations decorating each node of the abstract
syntax tree. @Pattern@ is a 'Traversable' 'Comonad' over the type of
annotations.

-}
newtype Pattern
    (variable :: *)
    (annotation :: *)
  =
    Pattern
        { getPattern :: Cofree (PatternF variable) annotation }
    deriving (Foldable, Functor, GHC.Generic, Traversable)

instance Eq variable => Eq (Pattern variable annotation) where
    (==) = eqWorker
      where
        eqWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            pat1 == pat2
    {-# INLINE (==) #-}

instance Ord variable => Ord (Pattern variable annotation) where
    compare = compareWorker
      where
        compareWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            compare pat1 pat2
    {-# INLINE compare #-}

deriving instance
    (Show annotation, Show variable) =>
    Show (Pattern variable annotation)

instance Hashable variable => Hashable (Pattern variable annotation) where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance
    (NFData annotation, NFData variable) =>
    NFData (Pattern variable annotation)
  where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat

instance SOP.Generic (Pattern variable annotation)

instance SOP.HasDatatypeInfo (Pattern variable annotation)

instance
    (Debug annotation, Debug variable) =>
    Debug (Pattern variable annotation)

instance
    (Debug annotation, Debug variable, Diff annotation, Diff variable)
    => Diff (Pattern variable annotation)

instance
    (SortedVariable variable, Unparse variable) =>
    Unparse (Pattern variable annotation)
  where
    unparse (Recursive.project -> _ :< pat) = unparse pat
    unparse2 (Recursive.project -> _ :< pat) = unparse2 pat

type instance Base (Pattern variable annotation) =
    CofreeF (PatternF variable) annotation

-- This instance implements all class functions for the Pattern newtype
-- because the their implementations for the inner type may be specialized.
instance Recursive (Pattern variable annotation) where
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
instance Corecursive (Pattern variable annotation) where
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
instance Comonad (Pattern variable) where
    extract = \(Pattern fixed) -> extract fixed
    {-# INLINE extract #-}
    duplicate = \(Pattern fixed) -> Pattern (extend Pattern fixed)
    {-# INLINE duplicate #-}
    extend extending = \(Pattern fixed) ->
        Pattern (extend (extending . Pattern) fixed)
    {-# INLINE extend #-}

instance ComonadCofree (PatternF variable) (Pattern variable) where
    unwrap = \(Pattern fixed) -> Pattern <$> unwrap fixed
    {-# INLINE unwrap #-}

instance TopBottom (Pattern variable annotation) where
    isTop (Recursive.project -> _ :< TopF _) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomF _) = True
    isBottom _ = False

fromPattern
    :: Pattern variable annotation
    -> Base
        (Pattern variable annotation)
        (Pattern variable annotation)
fromPattern = Recursive.project

asPattern
    :: Base
        (Pattern variable annotation)
        (Pattern variable annotation)
    -> Pattern variable annotation
asPattern = Recursive.embed

-- | Erase the annotations from any 'Pattern'.
eraseAnnotations
    :: Pattern variable erased
    -> Pattern variable Attribute.Null
eraseAnnotations = (<$) Attribute.Null

{- | Use the provided traversal to replace all variables in a 'Pattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2 annotation.
        Monad m
    => (variable1 -> m variable2)
    -> Pattern variable1 annotation
    -> m (Pattern variable2 annotation)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker
        :: Base
            (Pattern variable1 annotation)
            (m (Pattern variable2 annotation))
        -> m (Pattern variable2 annotation)
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
    :: (variable1 -> variable2)
    -> Pattern variable1 annotation
    -> Pattern variable2 annotation
mapVariables mapping =
    Recursive.ana (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (a :< pat) =
        a :< PatternF.mapVariables mapping pat

{- | Construct a 'ConcretePattern' from a 'Pattern'.

A concrete pattern contains no variables, so @asConcretePattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcretePattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcretePattern
    :: Pattern variable annotation
    -> Maybe (Pattern Concrete annotation)
asConcretePattern = traverseVariables (\case { _ -> Nothing })

isConcrete :: Pattern variable annotation -> Bool
isConcrete = isJust . asConcretePattern

{- | Construct a 'Pattern' from a 'ConcretePattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcretePattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcretePattern
    :: Pattern Concrete annotation
    -> Pattern variable annotation
fromConcretePattern = mapVariables (\case {})
