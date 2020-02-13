{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshPartialOrd (..)
    , FreshVariable (..)
    , incrementVariable
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

Two variables are related under this partial order when @compareFresh@ returns
@'Just' _@.

Agreement:

prop> maybe True (== compare a b) (compareFresh a b)

Relevance:

prop> compareFresh a (supVariable a) \/= Nothing

prop> isJust (nextVariable x a) ==> isJust (compareFresh a (nextVariable x a))

prop> isJust (nextVariable x a) ==> isJust (compareFresh x (nextVariable x a))

Idempotence:

prop> supVariable a == supVariable (supVariable a)

Dominance:

prop> a \/= supVariable a ==> compareFresh a (supVariable a) == Just LT

Monotonicity:

prop> isJust (nextVariable x a) ==> compareFresh a (nextVariable x a) == Just LT

prop> isJust (nextVariable x a) ==> compareFresh x (nextVariable x a) == Just LT

Note: The monotonicity property of 'nextVariable' implies the relevance
property.

 -}
class Ord variable => FreshPartialOrd variable where
    {- | @compareFresh@ defines a partial order on variables.

    In the typical implementation of fresh name generation, the variable name
    consists of a string (the base name) and a counter. Then, all variables with
    the same base name are related, and their ordering is given by the counter.

     -}
    compareFresh :: variable -> variable -> Maybe Ordering

    {- | @supVariable x@ is the greatest variable related to @x@.

    In the typical implementation, the counter has type
    @'Maybe' ('Sup' 'Natural')@
    so that @supVariable x@ has a counter @'Just' 'Sup'@.

     -}
    supVariable :: variable -> variable

    {- | @nextVariable@ generates a fresh variable greater than a given bound.

    The resulting variable, if defined, is /related/ to the /original variable/.
    @nextVariable@ returns @'Nothing'@ unless:

    * the /lower bound/ is related to the /original variable/, and
    * the /original variable/ is not greater than the /lower bound/.

    When @nextVariable@ returns a value (@'Just' _@), then the result is
    strictly greater than both arguments.

     -}
    nextVariable
        :: variable  -- ^ lower bound
        -> variable  -- ^ original variable
        -> Maybe variable

incrementVariable :: FreshPartialOrd variable => variable -> variable
incrementVariable original =
    case nextVariable original original of
        Just incremented -> incremented
        Nothing ->
            -- This is impossible for any law-abiding instance of
            -- FreshPartialOrd.
            undefined

instance FreshPartialOrd Variable where
    compareFresh x y
      | variableName x == variableName y = Just $ compare x y
      | otherwise = Nothing
    {-# INLINE compareFresh #-}

    supVariable variable = variable { variableCounter = Just Sup }
    {-# INLINE supVariable #-}

    nextVariable bound original = do
        ordering <- compareFresh bound original
        case ordering of { LT -> empty; _ -> pure () }
        incrementCounter . resetIdLocation $ original
      where
        resetIdLocation =
            Lens.set
                (field @"variableName" . field @"idLocation")
                AstLocationGeneratedVariable
        incrementCounter =
            field @"variableCounter" $ \_ ->
                case variableCounter bound of
                    Nothing -> pure $ Just (Element 0)
                    Just (Element a) -> pure $ Just (Element (succ a))
                    Just Sup ->
                        -- Never rename (supVariable _) because it does not
                        -- occur in any pattern.
                        empty
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

    nextVariable (ElementVariable bound) (ElementVariable original) =
        ElementVariable <$> nextVariable bound original
    {-# INLINE nextVariable #-}

instance
    FreshPartialOrd variable
    => FreshPartialOrd (SetVariable variable)
  where
    compareFresh = on compareFresh getSetVariable
    {-# INLINE compareFresh #-}

    supVariable = SetVariable . supVariable . getSetVariable
    {-# INLINE supVariable #-}

    nextVariable (SetVariable bound) (SetVariable original) =
        SetVariable <$> nextVariable bound original
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
        -> variable      -- ^ variable to rename
        -> Maybe variable
    default refreshVariable
        :: FreshPartialOrd variable
        => Set variable
        -> variable
        -> Maybe variable
    refreshVariable avoiding original = do
        largest <- Set.lookupLT (supVariable original) avoiding
        _ <- compareFresh original largest
        nextVariable largest original
    {-# INLINE refreshVariable #-}

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
