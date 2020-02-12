{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshPartialOrd (..)
    , FreshVariable (..)
    , refreshVariables
    -- * Re-exports
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import qualified Data.Foldable as Foldable
import Data.Function
    ( on
    )
import Data.Functor
    ( ($>)
    )
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
import Kore.Syntax.ElementVariable
import Kore.Syntax.Id
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable

{- | @FreshPartialOrder@ defines a partial order for renaming variables.

Agreement:

prop> maybe True (== compare a b) (compareFresh a b)

Relevance:

prop> compareFresh a (supVariable a) \/= Nothing

prop> a \/= supVariable a && x \/= supVariable x ==> compareFresh a (nextVariable a x) \/= Nothing

Idempotence:

prop> supVariable a == supVariable (supVariable a)

Dominance:

prop> a \/= supVariable a ==> compareFresh a (supVariable a) == Just LT

Monotonicity:

prop> a \/= supVariable a && x \/= supVariable x ==> compareFresh a (nextVariable a x) == Just LT

Note: The monotonicity property of 'nextVariable' implies the relevance
property.

prop> a \/= supVariable a && x \/= supVariable x ==> maybe True (== LT) (compareFresh x (nextVariable a x))

 -}
class Ord variable => FreshPartialOrd variable where
    compareFresh :: variable -> variable -> Maybe Ordering
    supVariable :: variable -> variable
    nextVariable
        :: variable  -- ^ original variable
        -> variable  -- ^ lower bound
        -> variable

instance FreshPartialOrd Variable where
    compareFresh x y
      | variableName x == variableName y = Just $ compare x y
      | otherwise = Nothing
    {-# INLINE compareFresh #-}

    supVariable variable = variable { variableCounter = Just Sup }
    {-# INLINE supVariable #-}

    nextVariable variable Variable { variableCounter = boundary } =
        variable
        & Lens.set (field @"variableName" . field @"idLocation") generated
        & Lens.over (field @"variableCounter") (increment . max boundary)
      where
        generated = AstLocationGeneratedVariable
        increment =
            \case
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter
    {-# INLINE nextVariable #-}

instance FreshPartialOrd Concrete where
    compareFresh = \case {}
    supVariable = \case {}
    nextVariable = \case {}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (ElementVariable variable)
  where
    compareFresh = on compareFresh getElementVariable
    {-# INLINE compareFresh #-}

    supVariable = ElementVariable . supVariable . getElementVariable
    {-# INLINE supVariable #-}

    nextVariable (ElementVariable variable) (ElementVariable bound) =
        ElementVariable (nextVariable variable bound)
    {-# INLINE nextVariable #-}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (SetVariable variable)
  where
    compareFresh = on compareFresh getSetVariable
    {-# INLINE compareFresh #-}

    supVariable = SetVariable . supVariable . getSetVariable
    {-# INLINE supVariable #-}

    nextVariable (SetVariable variable) (SetVariable bound) =
        SetVariable (nextVariable variable bound)
    {-# INLINE nextVariable #-}

{- | A @FreshVariable@ can be renamed to avoid colliding with a set of names.
-}
class Ord variable => FreshVariable variable where
    {- | Refresh a variable, renaming it avoid the given set.

    If the given variable occurs in the set, @refreshVariable@ must return
    'Just' a fresh variable which does not occur in the set. If the given
    variable does /not/ occur in the set, @refreshVariable@ /may/ return
    'Nothing'.

     -}
    refreshVariable
        :: Set variable  -- ^ variables to avoid
        -> variable        -- ^ variable to rename
        -> Maybe variable
    default refreshVariable
        :: FreshPartialOrd variable
        => Set variable
        -> variable
        -> Maybe variable
    refreshVariable avoiding variable = do
        largest <- Set.lookupLT (supVariable variable) avoiding
        compareFresh variable largest $> nextVariable variable largest

instance FreshPartialOrd variable => FreshVariable (ElementVariable variable)

instance FreshPartialOrd variable => FreshVariable (SetVariable variable)

instance FreshVariable Variable

instance FreshVariable Concrete where
    refreshVariable _ = \case {}

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
    :: FreshVariable variable
    => Set variable  -- ^ variables to avoid
    -> Set variable  -- ^ variables to rename
    -> Map variable variable
refreshVariables avoid0 =
    snd <$> Foldable.foldl' refreshVariablesWorker (avoid0, Map.empty)
  where
    refreshVariablesWorker (avoid, rename) var
      | Just var' <- refreshVariable avoid var =
        let avoid' =
                -- Avoid the freshly-generated variable in future renamings.
                Set.insert var' avoid
            rename' =
                -- Record a mapping from the original variable to the
                -- freshly-generated variable.
                Map.insert var var' rename
        in (avoid', rename')
      | otherwise =
        -- The variable does not collide with any others, so renaming is not
        -- necessary.
        (Set.insert var avoid, rename)
