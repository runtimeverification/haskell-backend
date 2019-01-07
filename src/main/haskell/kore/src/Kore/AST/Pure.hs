{-|
Module      : Kore.AST.Pure
Description : Kore patterns specialized to a specific level
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com

-}
module Kore.AST.Pure
    ( PurePattern (..)
    , CommonPurePattern
    , ConcretePurePattern
    , ParsedPurePattern
    , asPurePattern
    , fromPurePattern
    , eraseAnnotations
    , traverseVariables
    , mapVariables
    , asConcretePurePattern
    , fromConcretePurePattern
    , castMetaDomainValues
    , castVoidDomainValues
    -- * Pure pattern heads
    , groundHead
    , constant
    -- * Pattern stubs
    , PurePatternStub
    , CommonPurePatternStub
    , applyUnsortedPurePatternStub
    -- * Re-exports
    , Base, CofreeF (..)
    , module Control.Comonad
    , module Kore.AST.Common
    , module Kore.AST.Identifier
    , module Kore.AST.MetaOrObject
    , module Kore.Sort
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
import           Data.Text
                 ( Text )
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Null as Annotation
import           Kore.Annotation.Valid
                 ( Valid (..) )
import           Kore.AST.Common hiding
                 ( castMetaDomainValues, castVoidDomainValues, mapDomainValues,
                 mapVariables, traverseVariables )
import qualified Kore.AST.Common as Head
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
import           Kore.Sort
import           Kore.TopBottom
                 ( TopBottom (..) )

{- | The abstract syntax of Kore at a fixed level @level@.

@dom@ is the type of domain values; see "Kore.Domain.External" and
"Kore.Domain.Builtin".

@var@ is the family of variable types, parameterized by level.

@ann@ is the type of annotations decorating each node of the abstract syntax
tree. @PurePattern@ is a 'Traversable' 'Comonad' over the type of annotations.

-}
newtype PurePattern
    (level :: *)
    (domain :: * -> *)
    (variable :: * -> *)
    (annotation :: *)
  =
    PurePattern
        { getPurePattern :: Cofree (Pattern level domain variable) annotation }
    deriving (Foldable, Functor, Generic, Traversable)

instance
    ( Eq level
    , Eq (variable level)
    , Eq1 domain, Functor domain
    ) =>
    Eq (PurePattern level domain variable annotation)
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
    ( Ord level
    , Ord (variable level)
    , Ord1 domain, Functor domain
    ) =>
    Ord (PurePattern level domain variable annotation)
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
    , Show (variable level)
    , Show1 domain
    , child ~ Cofree (Pattern level domain variable) annotation
    ) =>
    Show (PurePattern level domain variable annotation)

instance
    ( Functor domain
    , Hashable (variable level)
    , Hashable (domain child)
    , child ~ PurePattern level domain variable annotation
    ) =>
    Hashable (PurePattern level domain variable annotation)
  where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance
    ( Functor domain
    , NFData annotation
    , NFData (variable level)
    , NFData (domain child)
    , child ~ PurePattern level domain variable annotation
    ) =>
    NFData (PurePattern level domain variable annotation)
  where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat `seq` ()

type instance Base (PurePattern level domain variable annotation) =
    CofreeF (Pattern level domain variable) annotation

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Recursive (PurePattern level domain variable annotation)
  where
    project = \(PurePattern embedded) ->
        case Recursive.project embedded of
            Compose (Identity projected) -> PurePattern <$> projected
    {-# INLINE project #-}

    -- This specialization is particularly important: The default implementation
    -- of 'cata' in terms of 'project' would involve an extra call to 'fmap' at
    -- every level of the tree due to the implementation of 'project' above.
    cata alg = \(PurePattern fixed) ->
        Recursive.cata
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE cata #-}

    para alg = \(PurePattern fixed) ->
        Recursive.para
            (\(Compose (Identity base)) ->
                 alg (Bifunctor.first PurePattern <$> base)
            )
            fixed
    {-# INLINE para #-}

    gpara dist alg = \(PurePattern fixed) ->
        Recursive.gpara
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> alg (Env.local PurePattern <$> base))
            fixed
    {-# INLINE gpara #-}

    prepro pre alg = \(PurePattern fixed) ->
        Recursive.prepro
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE prepro #-}

    gprepro dist pre alg = \(PurePattern fixed) ->
        Recursive.gprepro
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE gprepro #-}

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Corecursive (PurePattern level domain variable annotation)
  where
    embed = \projected ->
        (PurePattern . Recursive.embed . Compose . Identity)
            (getPurePattern <$> projected)
    {-# INLINE embed #-}

    ana coalg = PurePattern . ana0
      where
        ana0 =
            Recursive.ana (Compose . Identity . coalg)
    {-# INLINE ana #-}

    apo coalg = PurePattern . apo0
      where
        apo0 =
            Recursive.apo
                (\a ->
                     (Compose . Identity)
                        (Bifunctor.first getPurePattern <$> coalg a)
                )
    {-# INLINE apo #-}

    postpro post coalg = PurePattern . postpro0
      where
        postpro0 =
            Recursive.postpro
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE postpro #-}

    gpostpro dist post coalg = PurePattern . gpostpro0
      where
        gpostpro0 =
            Recursive.gpostpro
                (Compose . Identity . dist . (<$>) (runIdentity . getCompose))
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE gpostpro #-}

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Comonad (PurePattern level domain variable)
  where
    extract = \(PurePattern fixed) -> extract fixed
    {-# INLINE extract #-}
    duplicate = \(PurePattern fixed) -> PurePattern (extend PurePattern fixed)
    {-# INLINE duplicate #-}
    extend extending = \(PurePattern fixed) ->
        PurePattern (extend (extending . PurePattern) fixed)
    {-# INLINE extend #-}

instance
    Functor domain =>
    ComonadCofree
        (Pattern level domain variable)
        (PurePattern level domain variable)
  where
    unwrap = \(PurePattern fixed) -> PurePattern <$> unwrap fixed
    {-# INLINE unwrap #-}

instance Functor domain
    => TopBottom (PurePattern level domain variable annotation)
  where
    isTop (Recursive.project -> _ :< TopPattern Top {}) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomPattern Bottom {}) = True
    isBottom _ = False

fromPurePattern
    :: Functor domain
    => PurePattern level domain variable annotation
    -> Base
        (PurePattern level domain variable annotation)
        (PurePattern level domain variable annotation)
fromPurePattern = Recursive.project

asPurePattern
    :: Functor domain
    => Base
        (PurePattern level domain variable annotation)
        (PurePattern level domain variable annotation)
    -> PurePattern level domain variable annotation
asPurePattern = Recursive.embed

-- | Erase the annotations from any 'PurePattern'.
eraseAnnotations
    :: Functor domain
    => PurePattern level domain variable erased
    -> PurePattern level domain variable (Annotation.Null level)
eraseAnnotations = (<$) Annotation.Null

-- | A pure pattern at level @level@ with variables in the common 'Variable'.
type CommonPurePattern level domain =
    PurePattern level domain Variable (Annotation.Null level)

-- | A concrete pure pattern (containing no variables) at level @lvl@.
type ConcretePurePattern level domain =
    PurePattern level domain Concrete (Valid (Concrete level) level)

-- | A pure pattern which has only been parsed and lacks 'Valid' annotations.
type ParsedPurePattern level domain =
    PurePattern level domain Variable (Annotation.Null level)

{- | Use the provided traversal to replace all variables in a 'PurePattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m level variable1 variable2 domain annotation.
        (Monad m, Traversable domain)
    => (variable1 level -> m (variable2 level))
    -> PurePattern level domain variable1 annotation
    -> m (PurePattern level domain variable2 annotation)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker
        :: Base
            (PurePattern level domain variable1 annotation)
            (m (PurePattern level domain variable2 annotation))
        -> m (PurePattern level domain variable2 annotation)
    traverseVariablesWorker (a :< pat) =
        reannotate <$> (Head.traverseVariables traversing =<< sequence pat)
      where
        reannotate pat' = Recursive.embed (a :< pat')

{- | Use the provided mapping to replace all variables in a 'PurePattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

See also: 'traverseVariables'

 -}
mapVariables
    :: Functor domain
    => (variable1 level -> variable2 level)
    -> PurePattern level domain variable1 annotation
    -> PurePattern level domain variable2 annotation
mapVariables mapping =
    Recursive.ana (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (a :< pat) =
        a :< Head.mapVariables mapping pat

-- | Use the provided mapping to replace all domain values in a 'PurePattern'.
mapDomainValues
    ::  forall level domain1 domain2 variable annotation.
        (Functor domain1, Functor domain2)
    => (forall child. domain1 child -> domain2 child)
    -> PurePattern level domain1 variable annotation
    -> PurePattern level domain2 variable annotation
mapDomainValues mapping =
    -- Using 'Recursive.unfold' so that the pattern will unfold lazily.
    -- Lazy unfolding allows composing multiple tree transformations without
    -- allocating the entire intermediates.
    Recursive.unfold (mapDomainValuesWorker . Recursive.project)
  where
    mapDomainValuesWorker (a :< pat) =
        a :< Head.mapDomainValues mapping pat

{- | Construct a 'ConcretePurePattern' from a 'PurePattern'.

A concrete pattern contains no variables, so @asConcretePurePattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcretePurePattern@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcretePurePattern
    :: forall level domain variable annotation. Traversable domain
    => PurePattern level domain variable annotation
    -> Maybe (PurePattern level domain Concrete annotation)
asConcretePurePattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'PurePattern' from a 'ConcretePurePattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcretePurePattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcretePurePattern
    :: forall level domain variable annotation. Functor domain
    => PurePattern level domain Concrete annotation
    -> PurePattern level domain variable annotation
fromConcretePurePattern = mapVariables (\case {})

{- | Cast a pure pattern with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: Functor domain
    => PurePattern level (Const Void) variable annotation
    -> PurePattern level domain variable annotation
castVoidDomainValues = mapDomainValues (\case {})

{- | Cast a 'Meta'-pure-pattern into any domain.

The pattern can be cast trivially because it meta-patterns contain no
domain values.

 -}
castMetaDomainValues
    :: (Functor domain1, Functor domain2)
    => PurePattern Meta domain1 variable annotation
    -> PurePattern Meta domain2 variable annotation
castMetaDomainValues =
    Recursive.ana (castMetaDomainValuesWorker . Recursive.project)
  where
    castMetaDomainValuesWorker (a :< pat) =
        a :< Head.castMetaDomainValues pat

-- |Given an 'Id', 'groundHead' produces the head of an 'Application'
-- corresponding to that argument.
groundHead :: Text -> AstLocation -> SymbolOrAlias level
groundHead ctor location = SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = ctor
        , idLocation = location
        }
    , symbolOrAliasParams = []
    }

-- |Given a head and a list of children, produces an 'ApplicationPattern'
--  applying the given head to the children
apply :: SymbolOrAlias level -> [child] -> Pattern level domain variable child
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

-- |Applies the given head to the empty list of children to obtain a
-- constant 'ApplicationPattern'
constant
    :: SymbolOrAlias level -> Pattern level domain variable child
constant patternHead = apply patternHead []

type PurePatternStub level domain variable annotation =
    PatternStub
        level
        domain
        variable
        (PurePattern level domain variable annotation)

type CommonPurePatternStub level domain =
    PurePatternStub level domain Variable (Annotation.Null level)

{- | Construct a 'PurePattern' by applying a sort to an unsorted stub.
 -}
applyUnsortedPurePatternStub
    ::  ( Functor domain
        , result ~ PurePattern level domain variable (Annotation.Null level)
        )
    => (Sort level -> Pattern level domain variable result)
    -- ^ Unsorted pattern stub
    -> Sort level
    -- ^ Target sort
    -> result
applyUnsortedPurePatternStub stub patternSort =
    asPurePattern (mempty :< stub patternSort)
