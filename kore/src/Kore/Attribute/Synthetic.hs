{- |
Description : Attribute grammars implemented as cofree annotations
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Synthetic
    ( Synthetic (..)
    , synthesize, synthesizeAux
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Foldable as Foldable
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive

import           Kore.Attribute.Pattern.FreeVariables
                 ( FreeVariables (..) )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import           Kore.Domain.Builtin
                 ( builtinSort )
import           Kore.Internal.TermLike
                 ( Evaluated (..), TermLikeF (..) )
import           Kore.Sort
import           Kore.Syntax.DomainValue
import           Kore.Syntax.Exists
import           Kore.Syntax.Forall
import           Kore.Syntax.Mu
import           Kore.Syntax.Next
import           Kore.Syntax.Not
import           Kore.Syntax.Nu
import           Kore.Syntax.SetVariable
import           Kore.Syntax.Variable

{- | @Synthetic@ is the class of synthetic attribute types @syn@.

@Synthetic base inh syn@ allows synthesizing @syn@ given a @'Cofree' base inh@
tree; that is, a 'Cofree' tree with branching described by a @'Functor' base@
with attributes @inh@ at its nodes.

 -}
class Functor base => Synthetic base inh syn where
    {- | @synthetic@ is the @base@-algebra for synthesizing the attribute @syn@.

    The algebra may inherit an attribute of type @inh@, but that may change in
    the future.

     -}
    synthetic :: CofreeF base inh syn -> syn

instance
    Ord variable =>
    Synthetic (TermLikeF variable) inh (FreeVariables variable)
  where
    synthetic (_ :< termLikeF) =
        case termLikeF of
            -- Not implemented
            ApplyAliasF _ -> undefined
            -- Binders
            ExistsF existsF -> FreeVariables.delete existsVariable existsChild
              where
                Exists { existsVariable, existsChild } = existsF
            ForallF forallF -> FreeVariables.delete forallVariable forallChild
              where
                Forall { forallVariable, forallChild } = forallF
            VariableF variableF -> FreeVariables.singleton variableF
            --
            _ -> Foldable.fold termLikeF
    {-# INLINE synthetic #-}

-- TODO (thomas.tuegel): Do not take an input sort here.
instance
    SortedVariable variable =>
    Synthetic (TermLikeF variable) Sort Sort
  where
    synthetic (inputSort :< termLikeF) =
        case termLikeF of
            -- Not checked
            ApplyAliasF _ -> inputSort
            ApplySymbolF _ -> inputSort
            -- Predicates
            BottomF _ -> inputSort
            CeilF _ -> inputSort
            FloorF _ -> inputSort
            TopF _ -> inputSort
            EqualsF equalsF -> seq (alignSorts equalsF) inputSort
            InF inF -> seq (alignSorts inF) inputSort
            -- Connectives
            AndF andF -> alignSorts andF
            IffF iffF -> alignSorts iffF
            ImpliesF impliesF -> alignSorts impliesF
            OrF orF -> alignSorts orF
            RewritesF rewritesF -> alignSorts rewritesF
            -- Nothing to check
            DomainValueF domainValueF -> domainValueSort domainValueF
            ExistsF existsF -> existsChild existsF
            ForallF forallF -> forallChild forallF
            MuF muF -> muChild muF
            NextF nextF -> nextChild nextF
            NotF notF -> notChild notF
            NuF nuF -> nuChild nuF
            StringLiteralF _ -> stringMetaSort
            CharLiteralF _ -> charMetaSort
            VariableF variableF -> sortedVariableSort variableF
            InhabitantF inhF -> inhF
            SetVariableF setVariableF ->
                sortedVariableSort (getVariable setVariableF)
            BuiltinF builtinF -> builtinSort builtinF
            EvaluatedF evaluatedF -> getEvaluated evaluatedF

{- | @/synthesize/@ attribute @b@ bottom-up along a tree @s@.

@synthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree @s@
with attributes @inh@ along the nodes, @synthesize@ produces a tree @t@ with
attributes @syn@ along the nodes using the given @('Base' s)@-algebra from the
bottom up.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
synthesize
    ::  ( Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF base inh
        , Base t ~ CofreeF base syn
        , Synthetic base inh syn
        )
    => s  -- ^ Original tree with attributes @a@
    -> t
synthesize = synthesizeAux synthetic

{-# INLINE synthesize #-}

{- | @/synthesize/@ attribute @b@ bottom-up along a tree @s@.

@synthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree @s@
with attributes @a@ along the nodes, @synthesize@ produces a tree @t@ with
attributes @b@ along the nodes using the given @(Base s)@-algebra from the
bottom up. The algebra's argument is the original @a@-attribute of a node and
the @b@-attributes of all children.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
synthesizeAux
    ::  ( Functor f
        , Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF f a
        , Base t ~ CofreeF f b
        )
    => (CofreeF f a b -> b)  -- ^ @(Base s)@-algebra synthesizing @b@
    -> s  -- ^ Original tree with attributes @a@
    -> t
synthesizeAux synth =
    Recursive.fold worker
  where
    worker (a :< ft) =
        Recursive.embed (synth (a :< fb) :< ft)
      where
        fb = Cofree.headF . Recursive.project <$> ft

{-# INLINE synthesizeAux #-}
