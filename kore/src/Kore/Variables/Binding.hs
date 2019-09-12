{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Variables.Binding
    ( Binding (..)
    , matchWith
    -- * Binders
    , Binder (..)
    , existsBinder
    , forallBinder
    , muBinder
    , nuBinder
    ) where

import Control.Comonad.Trans.Env
import qualified Control.Lens as Lens
import Data.Monoid
    ( Any (..)
    )

import Kore.Syntax.Exists
import Kore.Syntax.Forall
import Kore.Syntax.Mu
import Kore.Syntax.Nu
import Kore.Variables.UnifiedVariable

{- | @Binding@ defines traversals for patterns with binders.

@traverseBinder@ and @traverseVariable@ should be empty if the pattern is not
respectively a binder or a variable at the top level.

 -}
class Show patternType => Binding patternType where
    -- | The type of variables bound in @patternType@.
    type VariableType patternType

    -- | Traverse the binder at the top of a pattern.
    traverseBinder
        ::  Lens.Traversal' patternType
                (Binder (VariableType patternType) patternType)

    -- | Traverse the variable at the top of a pattern.
    traverseVariable
        :: Lens.Traversal'
            patternType
            (VariableType patternType)

{- | Apply a traversing function while distinguishing an empty 'Lens.Traversal'.

The result is 'Nothing' if the 'Lens.Traversal' is empty, or 'Just' if the
traversing function was ever applied.

 -}
matchWith
    :: Applicative f
    => Lens.ATraversal s t a b  -- ^ 'Lens.Traversal'
    -> (a -> f b)  -- ^ Traversing function
    -> s -> Maybe (f t)
matchWith (Lens.cloneTraversal -> traverse') = \afb s ->
    let (getAny -> matched, ft) = runEnvT (traverse' (EnvT (Any True) . afb) s)
    in if matched then Just ft else Nothing

-- | @Binder@ abstracts over binders such as 'Exists' and 'Forall'.
data Binder variable child = Binder
    { binderVariable :: variable, binderChild :: !child }

{- | A 'Lens.Lens' to view an 'Exists' as a 'Binder'.

@existsBinder@ may be used to implement 'traverseBinder'.

See also: 'forallBinder'.

 -}
existsBinder
    :: Lens.Lens'
        (Exists sort variable child)
        (Binder (UnifiedVariable variable) child)
existsBinder mapping exists =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable =  ElemVar existsVariable, binderChild }
      where
        Exists { existsVariable } = exists
        Exists { existsChild    = binderChild    } = exists
    finish binder' =
        exists { existsVariable, existsChild }
      where
        Binder { binderVariable = ElemVar existsVariable } = binder'
        Binder { binderChild    = existsChild    } = binder'

{- | A 'Lens.Lens' to view a 'Forall' as a 'Binder'.

@forallBinder@ may be used to implement 'traverseBinder'.

See also: 'existsBinder'.

 -}
forallBinder
    :: Lens.Lens'
        (Forall sort variable child)
        (Binder (UnifiedVariable variable) child)
forallBinder mapping forall =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable = ElemVar forallVariable, binderChild }
      where
        Forall { forallVariable } = forall
        Forall { forallChild    = binderChild    } = forall
    finish binder' =
        forall { forallVariable, forallChild }
      where
        Binder { binderVariable = ElemVar forallVariable } = binder'
        Binder { binderChild    = forallChild    } = binder'

{- | A 'Lens.Lens' to view a 'Mu' as a 'Binder'.

@muBinder@ may be used to implement 'traverseBinder'.

See also: 'nuBinder'.

 -}
muBinder
    :: Lens.Lens'
        (Mu variable child)
        (Binder (UnifiedVariable variable) child)
muBinder mapping mu =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable = SetVar muVariable, binderChild }
      where
        Mu { muVariable } = mu
        Mu { muChild    = binderChild    } = mu
    finish binder' =
        mu { muVariable, muChild }
      where
        Binder { binderVariable = SetVar muVariable } = binder'
        Binder { binderChild    = muChild    } = binder'

{- | A 'Lens.Lens' to view a 'Nu' as a 'Binder'.

@nuBinder@ may be used to implement 'traverseBinder'.

See also: 'muBinder'.

 -}
nuBinder
    :: Lens.Lens'
        (Nu variable child)
        (Binder (UnifiedVariable variable) child)
nuBinder mapping nu =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable = SetVar nuVariable, binderChild }
      where
        Nu { nuVariable } = nu
        Nu { nuChild    = binderChild    } = nu
    finish binder' =
        nu { nuVariable, nuChild }
      where
        Binder { binderVariable = SetVar nuVariable } = binder'
        Binder { binderChild    = nuChild    } = binder'
