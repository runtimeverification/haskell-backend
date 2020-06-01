{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshPartialOrd (..)
    , FreshName (..)
    , defaultRefreshName
    , refreshVariable
    , refreshElementVariable
    , refreshSetVariable
    , refreshVariables
    -- * Re-exports
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
import Data.Generics.Product
    ( field
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import Data.Sup
import Kore.Sort
import Kore.Syntax.Variable
import Kore.Variables.UnifiedVariable

{- | @FreshPartialOrder@ defines a partial order for renaming variables.

Two variables @x@ and @y@ are related under the partial order if @infVariable@
and @supVariable@ give the same value on @x@ and @y@.

Disjoint:

prop> infVariable x /= supVariable y

prop> (infVariable x == infVariable y) == (supVariable x == supVariable y)

Order:

prop> infVariable x <= x

prop> x <= supVariable x

prop> infVariable x < supVariable x

Idempotence:

prop> infVariable x == infVariable (infVariable x)

prop> supVariable x == supVariable (supVariable x)

Monotonicity:

prop> x < supVariable x ==> x < nextVariable x

Bounding:

prop> x < supVariable x ==> infVariable x < nextVariable x

prop> x < supVariable x ==> nextVariable x < supVariable x

 -}
class Ord variable => FreshPartialOrd variable where
    infVariable :: variable -> variable

    {- | @supVariable x@ is the greatest variable related to @x@.

    In the typical implementation, the counter has type
    @'Maybe' ('Sup' 'Natural')@
    so that @supVariable x@ has a counter @'Just' 'Sup'@.

     -}
    supVariable :: variable -> variable

    {- | @nextVariable@ increments the counter attached to a variable.
     -}
    nextVariable :: variable -> variable

instance FreshPartialOrd VariableName where
    infVariable variable = variable { counter = Nothing }
    {-# INLINE infVariable #-}

    supVariable variable = variable { counter = Just Sup }
    {-# INLINE supVariable #-}

    nextVariable =
        Lens.over (field @"counter") incrementCounter
        . Lens.set (field @"base" . field @"idLocation") generated
      where
        generated = AstLocationGeneratedVariable
        incrementCounter counter =
            case counter of
                Nothing          -> Just (Element 0)
                Just (Element n) -> Just (Element (succ n))
                Just Sup         -> illegalVariableCounter
    {-# INLINE nextVariable #-}

instance FreshPartialOrd Void where
    infVariable = \case {}
    supVariable = \case {}
    nextVariable = \case {}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (ElementVariableName variable)
  where
    infVariable = fmap infVariable
    {-# INLINE infVariable #-}

    supVariable = fmap supVariable
    {-# INLINE supVariable #-}

    nextVariable = fmap nextVariable
    {-# INLINE nextVariable #-}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (SetVariableName variable)
  where
    infVariable = fmap infVariable
    {-# INLINE infVariable #-}

    supVariable = fmap supVariable
    {-# INLINE supVariable #-}

    nextVariable = fmap nextVariable
    {-# INLINE nextVariable #-}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (SomeVariableName variable)
  where
    infVariable = fmap infVariable
    {-# INLINE infVariable #-}

    supVariable = fmap supVariable
    {-# INLINE supVariable #-}

    nextVariable = fmap nextVariable
    {-# INLINE nextVariable #-}

{- | A @FreshName@ can be renamed to avoid colliding with a set of names.
-}
class Ord name => FreshName name where
    {- | Refresh a name, renaming it avoid the given set.

    If the given name occurs in the set, @refreshName@ must return
    'Just' a fresh name which does not occur in the set. If the given
    name does /not/ occur in the set, @refreshName@ /may/ return
    'Nothing'.

     -}
    refreshName
        :: Set name  -- ^ names to avoid
        -> name      -- ^ original name
        -> Maybe name
    default refreshName
        :: FreshPartialOrd name
        => Set name
        -> name
        -> Maybe name
    refreshName = defaultRefreshName
    {-# INLINE refreshName #-}

defaultRefreshName
    :: FreshPartialOrd variable
    => Set variable
    -> variable
    -> Maybe variable
defaultRefreshName avoiding original = do
    let sup = supVariable original
    largest <- Set.lookupLT sup avoiding
    -- assignSort must not change the order with respect to sup.
    assert (largest < sup) $ Monad.guard (largest >= infVariable original)
    let next = nextVariable largest
    -- nextVariable must yield a variable greater than largest.
    assert (next > largest) $ pure next
{-# INLINE defaultRefreshName #-}

instance FreshName Void where
    refreshName _ = \case {}
    {-# INLINE refreshName #-}

instance FreshName VariableName

instance FreshPartialOrd variable => FreshName (ElementVariableName variable)

instance FreshPartialOrd variable => FreshName (SetVariableName variable)

instance FreshPartialOrd variable => FreshName (SomeVariableName variable)

refreshVariable
    :: FreshName variable
    => Set variable
    -> Variable1 variable
    -> Maybe (Variable1 variable)
refreshVariable avoiding = traverse (refreshName avoiding)
{-# INLINE refreshVariable #-}

refreshElementVariable
    :: FreshName (SomeVariableName variable)
    => Set (SomeVariableName variable)
    -> ElementVariable variable
    -> Maybe (ElementVariable variable)
refreshElementVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- SomeVariable1 (above) conserves the ElemVar constructor.
    fmap expectElemVar . refreshVariable avoiding . inject

refreshSetVariable
    :: FreshName (SomeVariableName variable)
    => Set (SomeVariableName variable)
    -> SetVariable variable
    -> Maybe (SetVariable variable)
refreshSetVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- SomeVariable1 (above) conserves the SetVar constructor.
    fmap expectSetVar . refreshVariable avoiding . inject

{- | Rename one set of variables while avoiding another.

If any of the variables to rename occurs in the set of avoided variables, it
will be mapped to a fresh name in the result. Every fresh name in the result
will also be unique among the fresh names.

To use @refreshVariables@ with 'Kore.Internal.Pattern.substitute', map the
result with 'Kore.Internal.TermLike.mkVar':

@
'Kore.Internal.TermLike.substitute'
    ('Kore.Internal.TermLike.mkVar' \<$\> refreshVariables avoid rename)
    :: 'Kore.Internal.TermLike.TermLike' Variable
    -> 'Kore.Internal.TermLike.TermLike' Variable
@

 -}
refreshVariables
    :: FreshName variable
    => Set variable  -- ^ variables to avoid
    -> Set (Variable1 variable)  -- ^ variables to rename
    -> Map variable (Variable1 variable)
refreshVariables avoid0 =
    snd <$> Foldable.foldl' refreshVariablesWorker (avoid0, Map.empty)
  where
    refreshVariablesWorker (avoid, rename) var
      | Just var' <- refreshVariable avoid var =
        let avoid' =
                -- Avoid the freshly-generated variable in future renamings.
                Set.insert (variableName1 var') avoid
            rename' =
                -- Record a mapping from the original variable to the
                -- freshly-generated variable.
                Map.insert (variableName1 var) var' rename
        in (avoid', rename')
      | otherwise =
        -- The variable does not collide with any others, so renaming is not
        -- necessary.
        (Set.insert (variableName1 var) avoid, rename)
