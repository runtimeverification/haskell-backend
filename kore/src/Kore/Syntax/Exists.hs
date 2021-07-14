{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Syntax.Exists (
    Exists (..),
    refreshExists,
    existsBinder,
) where

import qualified Control.Lens as Lens
import Data.Set (
    Set,
 )
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

{- |'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'existsSort' is both the sort of the operands and the sort of the result.
-}
data Exists sort variable child = Exists
    { existsSort :: !sort
    , existsVariable :: !(ElementVariable variable)
    , existsChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    (Unparse variable, Unparse child) =>
    Unparse (Exists Sort variable child)
    where
    unparse Exists{existsSort, existsVariable, existsChild} =
        "\\exists"
            <> parameters [existsSort]
            <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists{existsVariable, existsChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\exists"
                , unparse2SortedVariable existsVariable
                , unparse2 existsChild
                ]
            )

instance
    (Unparse variable, Unparse child) =>
    Unparse (Exists () variable child)
    where
    unparse Exists{existsVariable, existsChild} =
        "\\exists"
            <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists{existsVariable, existsChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\exists"
                , unparse2SortedVariable existsVariable
                , unparse2 existsChild
                ]
            )

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Exists sort variable)
    where
    synthetic Exists{existsVariable, existsChild} =
        bindVariable (inject existsVariable) existsChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Exists Sort variable) where
    synthetic Exists{existsSort, existsChild} =
        existsSort `matchSort` existsChild
    {-# INLINE synthetic #-}

instance
    (Ord variable, HasFreeVariables child variable) =>
    HasFreeVariables (Exists sort variable child) variable
    where
    freeVariables Exists{existsVariable, existsChild} =
        bindVariable (inject existsVariable) (freeVariables existsChild)

{- | A 'Lens.Lens' to view an 'Exists' as a 'Binder'.

@existsBinder@ may be used to implement 'traverseBinder'.

See also: 'forallBinder'.
-}
existsBinder ::
    Lens.Lens
        (Exists sort variable1 child1)
        (Exists sort variable2 child2)
        (Binder (ElementVariable variable1) child1)
        (Binder (ElementVariable variable2) child2)
existsBinder mapping exists =
    finish <$> mapping binder
  where
    binder =
        Binder
            { binderVariable = existsVariable
            , binderChild = existsChild
            }
      where
        Exists{existsVariable, existsChild} = exists
    finish Binder{binderVariable, binderChild} =
        exists{existsVariable = binderVariable, existsChild = binderChild}

refreshExists ::
    forall sort variable child.
    Substitute child =>
    VariableNameType child ~ variable =>
    FreshPartialOrd variable =>
    Set (SomeVariableName variable) ->
    Exists sort variable child ->
    Exists sort variable child
refreshExists extraAvoid existsF =
    Lens.over existsBinder (refreshElementBinder avoid) existsF
  where
    avoid = freeVariableNames existsF <> extraAvoid
{-# INLINE refreshExists #-}
