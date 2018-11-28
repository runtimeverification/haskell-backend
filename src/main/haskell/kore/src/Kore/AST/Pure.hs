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
    , module Kore.AST.MetaOrObject
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
import           Kore.AST.MetaOrObject

{- | The abstract syntax of Kore at a fixed level @lvl@.

@dom@ is the type of domain values; see "Kore.Domain.External" and
"Kore.Domain.Builtin".

@var@ is the family of variable types, parameterized by level.

@ann@ is the type of annotations decorating each node of the abstract syntax
tree. @PurePattern@ is a 'Traversable' 'Comonad' over the type of annotations.

-}
newtype PurePattern
    (lvl :: *)
    (dom :: * -> *)
    (var :: * -> *)
    (ann :: *)
  =
    PurePattern { getPurePattern :: Cofree (Pattern lvl dom var) ann }
    deriving (Foldable, Functor, Generic, Traversable)

instance
    ( Eq ann
    , Eq lvl
    , Eq (var lvl)
    , Eq1 dom, Functor dom
    ) =>
    Eq (PurePattern lvl dom var ann)
  where
    (==) = eqWorker
      where
        eqWorker
            (Recursive.project -> ann1 :< pat1)
            (Recursive.project -> ann2 :< pat2)
          =
            ann1 == ann2 && liftEq eqWorker pat1 pat2

instance
    ( Ord ann
    , Ord lvl
    , Ord (var lvl)
    , Ord1 dom, Functor dom
    ) =>
    Ord (PurePattern lvl dom var ann)
  where
    compare = compareWorker
      where
        compareWorker
            (Recursive.project -> ann1 :< pat1)
            (Recursive.project -> ann2 :< pat2)
          =
            compare ann1 ann2 <> liftCompare compareWorker pat1 pat2

deriving instance
    ( Show ann
    , Show (var lvl)
    , Show (dom child)
    , child ~ Cofree (Pattern lvl dom var) ann
    ) =>
    Show (PurePattern lvl dom var ann)

instance
    ( Functor dom
    , Hashable ann
    , Hashable (var lvl)
    , Hashable (dom child)
    , child ~ PurePattern lvl dom var ann
    ) =>
    Hashable (PurePattern lvl dom var ann)
  where
    hashWithSalt salt (Recursive.project -> ann :< pat) =
        salt `hashWithSalt` ann `hashWithSalt` pat

instance
    ( Functor dom
    , NFData ann
    , NFData (var lvl)
    , NFData (dom child)
    , child ~ PurePattern lvl dom var ann
    ) =>
    NFData (PurePattern lvl dom var ann)
  where
    rnf (Recursive.project -> ann :< pat) =
        rnf ann `seq` rnf pat `seq` ()

type instance Base (PurePattern lvl dom var ann) =
    CofreeF (Pattern lvl dom var) ann

instance Functor dom => Recursive (PurePattern lvl dom var ann) where
    project (PurePattern embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> PurePattern <$> projected

instance Functor dom => Corecursive (PurePattern lvl dom var ann) where
    embed projected =
        (PurePattern . Recursive.embed . Compose . Identity)
            (getPurePattern <$> projected)

instance Functor dom => Comonad (PurePattern lvl dom var) where
    extract (PurePattern a) = extract a
    duplicate (PurePattern a) = PurePattern (extend PurePattern a)
    extend extending (PurePattern a) =
        PurePattern (extend (extending . PurePattern) a)

instance
    Functor dom =>
    ComonadCofree (Pattern lvl dom var) (PurePattern lvl dom var)
  where
    unwrap (PurePattern a) = PurePattern <$> unwrap a

fromPurePattern
    :: Functor dom
    => PurePattern lvl dom var ann
    -> Base (PurePattern lvl dom var ann) (PurePattern lvl dom var ann)
fromPurePattern = Recursive.project

asPurePattern
    :: Functor dom
    => Base (PurePattern lvl dom var ann) (PurePattern lvl dom var ann)
    -> PurePattern lvl dom var ann
asPurePattern = Recursive.embed

-- | A pure pattern at level @lvl@ with variables in the common 'Variable'.
type CommonPurePattern lvl dom = PurePattern lvl dom Variable

-- | A concrete pure pattern (containing no variables) at level @lvl@.
type ConcretePurePattern lvl dom = PurePattern lvl dom Concrete

{- | Use the provided traversal to replace all variables in a 'PurePattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'

 -}
traverseVariables
    :: forall f lvl dom var1 var2 ann. (Monad f, Traversable dom)
    => (var1 lvl -> f (var2 lvl))
    -> PurePattern lvl dom var1 ann
    -> f (PurePattern lvl dom var2 ann)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker
        :: Base
            (PurePattern lvl dom var1 ann)
            (f (PurePattern lvl dom var2 ann))
        -> f (PurePattern lvl dom var2 ann)
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
    :: Functor dom
    => (var1 lvl -> var2 lvl)
    -> PurePattern lvl dom var1 ann
    -> PurePattern lvl dom var2 ann
mapVariables mapping =
    Recursive.ana (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (a :< pat) =
        a :< Head.mapVariables mapping pat

-- | Use the provided mapping to replace all domain values in a 'PurePattern'.
mapDomainValues
    :: forall lvl dom1 dom2 var ann. (Functor dom1, Functor dom2)
    => (forall child. dom1 child -> dom2 child)
    -> PurePattern lvl dom1 var ann
    -> PurePattern lvl dom2 var ann
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
    :: forall lvl dom var ann. Traversable dom
    => PurePattern lvl dom var ann
    -> Maybe (ConcretePurePattern lvl dom ann)
asConcretePurePattern = traverseVariables (\case { _ -> Nothing })

{- | Construct a 'PurePattern' from a 'ConcretePurePattern'.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcretePurePattern@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcretePurePattern
    :: forall lvl dom var ann. Functor dom
    => ConcretePurePattern lvl dom ann
    -> PurePattern lvl dom var ann
fromConcretePurePattern = mapVariables (\case {})

{- | Cast a pure pattern with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: Functor dom
    => PurePattern lvl (Const Void) var ann
    -> PurePattern lvl dom var ann
castVoidDomainValues = mapDomainValues (\case {})

{- | Cast a 'Meta'-pure-pattern into any domain.

The pattern can be cast trivially because it meta-patterns contain no
domain values.

 -}
castMetaDomainValues
    :: (Functor dom1, Functor dom2)
    => PurePattern Meta dom1 var ann
    -> PurePattern Meta dom2 var ann
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

type PurePatternStub lvl dom var ann =
    PatternStub lvl dom var (PurePattern lvl dom var ann)

type CommonPurePatternStub lvl dom ann =
    PurePatternStub lvl dom Variable ann
