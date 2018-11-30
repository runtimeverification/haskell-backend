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
    , asPurePattern
    , fromPurePattern
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
    -- * Re-exports
    , Base, CofreeF (..)
    , module Kore.AST.Common
    , module Kore.AST.Identifier
    , module Kore.AST.MetaOrObject
    , module Kore.Sort
    ) where

import           Control.Comonad
import           Control.Comonad.Trans.Cofree
                 ( Cofree, CofreeF (..), ComonadCofree (..) )
import           Control.DeepSeq
                 ( NFData (..) )
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

import           Kore.AST.Common hiding
                 ( castMetaDomainValues, castVoidDomainValues, mapDomainValues,
                 mapVariables, traverseVariables )
import qualified Kore.AST.Common as Head
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
import           Kore.Sort

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

instance
    Functor domain =>
    Recursive (PurePattern level domain variable annotation)
  where
    project (PurePattern embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> PurePattern <$> projected

instance
    Functor domain =>
    Corecursive (PurePattern level domain variable annotation)
  where
    embed projected =
        (PurePattern . Recursive.embed . Compose . Identity)
            (getPurePattern <$> projected)

instance
    Functor domain =>
    Comonad (PurePattern level domain variable)
  where
    extract (PurePattern a) = extract a
    duplicate (PurePattern a) = PurePattern (extend PurePattern a)
    extend extending (PurePattern a) =
        PurePattern (extend (extending . PurePattern) a)

instance
    Functor domain =>
    ComonadCofree
        (Pattern level domain variable)
        (PurePattern level domain variable)
  where
    unwrap (PurePattern a) = PurePattern <$> unwrap a

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

-- | A pure pattern at level @level@ with variables in the common 'Variable'.
type CommonPurePattern level domain = PurePattern level domain Variable

-- | A concrete pure pattern (containing no variables) at level @lvl@.
type ConcretePurePattern level domain = PurePattern level domain Concrete

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
    -> Maybe (ConcretePurePattern level domain annotation)
asConcretePurePattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'PurePattern' from a 'ConcretePurePattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcretePurePattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcretePurePattern
    :: forall level domain variable annotation. Functor domain
    => ConcretePurePattern level domain annotation
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

type CommonPurePatternStub level domain annotation =
    PurePatternStub level domain Variable annotation
