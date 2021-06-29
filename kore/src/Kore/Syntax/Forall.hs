{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Syntax.Forall (
    Forall (..),
    forallBinder,
    refreshForall,
) where

import qualified Control.Lens as Lens
import Data.Set (Set)
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Substitute
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.Binding (
    Binder (..),
 )
import Kore.Variables.Fresh (FreshPartialOrd)
import Prelude.Kore
import qualified Pretty

{- |'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'forallSort' is both the sort of the operands and the sort of the result.
-}
data Forall sort variable child = Forall
    { forallSort :: !sort
    , forallVariable :: !(ElementVariable variable)
    , forallChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance (Unparse variable, Unparse child) => Unparse (Forall Sort variable child) where
    unparse Forall{forallSort, forallVariable, forallChild} =
        "\\forall"
            <> parameters [forallSort]
            <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall{forallVariable, forallChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\forall"
                , unparse2SortedVariable forallVariable
                , unparse2 forallChild
                ]
            )

instance (Unparse variable, Unparse child) => Unparse (Forall () variable child) where
    unparse Forall{forallVariable, forallChild} =
        "\\forall"
            <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall{forallVariable, forallChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\forall"
                , unparse2SortedVariable forallVariable
                , unparse2 forallChild
                ]
            )

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Forall sort variable)
    where
    synthetic Forall{forallVariable, forallChild} =
        bindVariable (inject forallVariable) forallChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Forall Sort variable) where
    synthetic Forall{forallSort, forallChild} =
        forallSort `matchSort` forallChild
    {-# INLINE synthetic #-}

{- | A 'Lens.Lens' to view a 'Forall' as a 'Binder'.

@forallBinder@ may be used to implement 'traverseBinder'.

See also: 'existsBinder'.
-}
forallBinder ::
    Lens.Lens
        (Forall sort variable1 child1)
        (Forall sort variable2 child2)
        (Binder (ElementVariable variable1) child1)
        (Binder (ElementVariable variable2) child2)
forallBinder mapping forall =
    finish <$> mapping binder
  where
    binder =
        Binder{binderVariable = forallVariable, binderChild}
      where
        Forall{forallVariable} = forall
        Forall{forallChild = binderChild} = forall
    finish Binder{binderVariable, binderChild} =
        forall{forallVariable = binderVariable, forallChild = binderChild}

refreshForall ::
    forall sort variable child.
    Substitute child =>
    VariableNameType child ~ variable =>
    FreshPartialOrd variable =>
    Set (SomeVariableName variable) ->
    Forall sort variable child ->
    Forall sort variable child
refreshForall avoid = Lens.over forallBinder (refreshElementBinder avoid)
{-# INLINE refreshForall #-}
