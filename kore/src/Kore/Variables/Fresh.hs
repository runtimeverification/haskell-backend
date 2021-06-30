{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
-}
module Kore.Variables.Fresh (
    FreshPartialOrd (..),
    FreshName (..),
    defaultRefreshName,
    refreshVariable,
    refreshElementVariable,
    refreshSetVariable,
    refreshVariables,
    refreshVariablesSet,
    refreshVariables',

    -- * Re-exports
    module Kore.Syntax.Variable,
) where

import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Control.Monad.State.Strict (
    runState,
 )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product (
    field,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.MonoTraversable
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Data.Sup
import Data.Void
import Kore.Sort
import Kore.Syntax.Variable
import Prelude.Kore

{- | @FreshPartialOrder@ defines a partial order for renaming variables.

Two variables @x@ and @y@ are related under the partial order if @minBoundName@
and @maxBoundName@ give the same value on @x@ and @y@.

Disjoint:

prop> minBoundName x /= maxBoundName y

prop> (minBoundName x == minBoundName y) == (maxBoundName x == maxBoundName y)

Order:

prop> minBoundName x <= x

prop> x <= maxBoundName x

prop> minBoundName x < maxBoundName x

Idempotence:

prop> minBoundName x == minBoundName (minBoundName x)

prop> maxBoundName x == maxBoundName (maxBoundName x)

Monotonicity:

prop> x < maxBoundName x ==> Just x < nextName x x

Bounding:

prop> x < maxBoundName x ==> Just (minBoundName x) < nextName x x

prop> x < maxBoundName x ==> nextName x x < Just (maxBoundName x)
-}
class Ord name => FreshPartialOrd name where
    minBoundName :: name -> name

    -- | @maxBoundName x@ is the greatest name related to @x@.
    --
    --    In the typical implementation, the counter has type
    --    @'Maybe' ('Sup' 'Natural')@
    --    so that @maxBoundName x@ has a counter @'Just' 'Sup'@.
    maxBoundName :: name -> name

    -- | @nextName a b@ is the least name greater than @a@ and @b@.
    --
    --    The result shares any properties (besides its name) with the first argument.
    nextName :: name -> name -> Maybe name

instance FreshPartialOrd VariableName where
    minBoundName variable = variable{counter = Nothing}
    {-# INLINE minBoundName #-}

    maxBoundName variable = variable{counter = Just Sup}
    {-# INLINE maxBoundName #-}

    nextName name1 name2 =
        name1
            & Lens.set (field @"counter") counter'
            & Lens.set (field @"base" . field @"idLocation") generated
            & Just
      where
        generated = AstLocationGeneratedVariable
        counter' =
            case Lens.view (field @"counter") name2 of
                Nothing -> Just (Element 0)
                Just (Element n) -> Just (Element (succ n))
                Just Sup -> illegalVariableCounter
    {-# INLINE nextName #-}

instance FreshPartialOrd Void where
    minBoundName = \case
    maxBoundName = \case
    nextName = \case

instance
    FreshPartialOrd variable =>
    FreshPartialOrd (ElementVariableName variable)
    where
    minBoundName = fmap minBoundName
    {-# INLINE minBoundName #-}

    maxBoundName = fmap maxBoundName
    {-# INLINE maxBoundName #-}

    nextName name1 (ElementVariableName name2) =
        traverse (flip nextName name2) name1
    {-# INLINE nextName #-}

instance
    FreshPartialOrd variable =>
    FreshPartialOrd (SetVariableName variable)
    where
    minBoundName = fmap minBoundName
    {-# INLINE minBoundName #-}

    maxBoundName = fmap maxBoundName
    {-# INLINE maxBoundName #-}

    nextName name1 (SetVariableName name2) =
        traverse (flip nextName name2) name1
    {-# INLINE nextName #-}

instance
    FreshPartialOrd variable =>
    FreshPartialOrd (SomeVariableName variable)
    where
    minBoundName = fmap minBoundName
    {-# INLINE minBoundName #-}

    maxBoundName = fmap maxBoundName
    {-# INLINE maxBoundName #-}

    nextName (SomeVariableNameElement name1) (SomeVariableNameElement name2) =
        SomeVariableNameElement <$> nextName name1 name2
    nextName (SomeVariableNameSet name1) (SomeVariableNameSet name2) =
        SomeVariableNameSet <$> nextName name1 name2
    nextName _ _ = Nothing
    {-# INLINE nextName #-}

-- | A @FreshName@ can be renamed to avoid colliding with a set of names.
class Ord name => FreshName name where
    -- | Refresh a name, renaming it avoid the given set.
    --
    --    If the given name occurs in the set, @refreshName@ must return
    --    'Just' a fresh name which does not occur in the set. If the given
    --    name does /not/ occur in the set, @refreshName@ /may/ return
    --    'Nothing'.
    refreshName ::
        -- | names to avoid
        Set name ->
        -- | original name
        name ->
        Maybe name
    default refreshName ::
        FreshPartialOrd name =>
        Set name ->
        name ->
        Maybe name
    refreshName = defaultRefreshName
    {-# INLINE refreshName #-}

defaultRefreshName ::
    FreshPartialOrd variable =>
    Set variable ->
    variable ->
    Maybe variable
defaultRefreshName avoiding original = do
    Monad.guard (Set.member original avoiding)
    let sup = maxBoundName original
    largest <- Set.lookupLT sup avoiding
    next <- nextName original largest
    -- nextName must yield a variable greater than largest.
    assert (next > largest) $ pure next
{-# INLINE defaultRefreshName #-}

instance FreshName Void where
    refreshName _ = \case
    {-# INLINE refreshName #-}

instance FreshName VariableName

instance FreshPartialOrd variable => FreshName (ElementVariableName variable)

instance FreshPartialOrd variable => FreshName (SetVariableName variable)

instance FreshPartialOrd variable => FreshName (SomeVariableName variable)

refreshVariable ::
    FreshName variable =>
    Set variable ->
    Variable variable ->
    Maybe (Variable variable)
refreshVariable avoiding = traverse (refreshName avoiding)
{-# INLINE refreshVariable #-}

refreshElementVariable ::
    FreshName (SomeVariableName variable) =>
    Set (SomeVariableName variable) ->
    ElementVariable variable ->
    Maybe (ElementVariable variable)
refreshElementVariable avoiding =
    -- expectElementVariable is safe because the FreshVariable instance of
    -- SomeVariable (above) conserves the ElemVar constructor.
    fmap expectElementVariable . refreshVariable avoiding . inject

refreshSetVariable ::
    FreshName (SomeVariableName variable) =>
    Set (SomeVariableName variable) ->
    SetVariable variable ->
    Maybe (SetVariable variable)
refreshSetVariable avoiding =
    -- expectElementVariable is safe because the FreshVariable instance of
    -- SomeVariable (above) conserves the SetVar constructor.
    fmap expectSetVariable . refreshVariable avoiding . inject

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
refreshVariables ::
    FreshName variable =>
    MonoTraversable variables =>
    Element variables ~ Variable variable =>
    -- | variables to avoid
    Set variable ->
    -- | variables to rename
    variables ->
    Map variable (Variable variable)
refreshVariables avoid variables =
    let (_, refreshed) = refreshVariables' avoid variables
     in Map.mapKeys variableName refreshed

refreshVariablesSet ::
    FreshName variable =>
    -- | variables to avoid
    Set variable ->
    -- | variables to rename
    Set (Variable variable) ->
    Map variable (Variable variable)
refreshVariablesSet avoid = refreshVariables avoid . Set.toList

refreshVariables' ::
    FreshName variable =>
    MonoTraversable variables =>
    Element variables ~ Variable variable =>
    -- | variables to avoid
    Set variable ->
    -- | variables to rename
    variables ->
    (variables, Map (Variable variable) (Variable variable))
refreshVariables' avoid0 variables =
    let (variables', (_, rename)) =
            runState (otraverse worker variables) (avoid0, Map.empty)
     in (variables', rename)
  where
    worker var = do
        (avoid, rename) <- State.get
        case refreshVariable avoid var of
            Just var' -> do
                let avoid' =
                        -- Avoid the freshly-generated variable in future
                        -- renamings.
                        Set.insert (variableName var') avoid
                    rename' =
                        -- Record a mapping from the original variable to the
                        -- freshly-generated variable.
                        Map.insert var var' rename
                State.put (avoid', rename')
                pure var'
            _ -> do
                -- The variable does not collide with any others, so renaming is
                -- not necessary.
                let avoid' = Set.insert (variableName var) avoid
                State.put (avoid', rename)
                pure var
