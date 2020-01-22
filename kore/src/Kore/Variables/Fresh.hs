{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , Renaming
    , refreshVariables
    -- * Re-exports
    , module Kore.Syntax.Variable
    ) where

import qualified Control.Lens.Combinators as Lens
import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
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
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{- | A @FreshVariable@ can be renamed to avoid colliding with a set of names.
-}
class (Ord variable, SortedVariable variable) => FreshVariable variable where
    -- New: The greatest lower bound on variables
    -- with the same name as the given variable.
    infVariable :: variable -> variable
    -- New: The least upper bound on variables
    -- with the same name as the given variable.
    supVariable :: variable -> variable
    -- New: The least variable greater than the given variable.
    nextVariable :: variable -> variable

    -- This is a default implementation in terms of the above.
    -- The default implementation is suitable for most types
    -- and does O(1) allocation.
    {- | Refresh a variable, renaming it avoid the given set.

    If the given variable occurs in the set, @refreshVariable@ must return
    'Just' a fresh variable which does not occur in the set. If the given
    variable does /not/ occur in the set, @refreshVariable@ /may/ return
    'Nothing'.

     -}
    refreshVariable
        :: Set variable
        -- ^ variables to avoid
        -> variable
        -- ^ variable to rename
        -> Maybe variable
    refreshVariable avoiding variable = do
        fixedLargest <-
            Lens.set lensVariableSort theSort
            <$> Set.lookupLT pivotMax avoiding
        Monad.guard (fixedLargest >= pivotMin)
        return (nextVariable fixedLargest)
      where
        pivotMax = supVariable variable
        pivotMin = infVariable variable
        theSort = Lens.view lensVariableSort variable


type Renaming variable =
    Map (UnifiedVariable variable) (UnifiedVariable variable)

instance FreshVariable variable => FreshVariable (ElementVariable variable)
  where
    infVariable = fmap infVariable
    supVariable = fmap supVariable
    nextVariable = fmap nextVariable

instance FreshVariable variable => FreshVariable (SetVariable variable)
  where
    infVariable = fmap infVariable
    supVariable = fmap supVariable
    nextVariable = fmap nextVariable

instance FreshVariable variable => FreshVariable (UnifiedVariable variable)
  where
    infVariable (ElemVar variable) =
        ElemVar . infVariable $ variable
    infVariable (SetVar variable) =
        SetVar . infVariable $ variable

    supVariable (ElemVar variable) =
        ElemVar . supVariable $ variable
    supVariable (SetVar variable) =
        SetVar . supVariable $ variable

    nextVariable (ElemVar variable) =
        ElemVar . nextVariable $ variable
    nextVariable (SetVar variable) =
        SetVar . nextVariable $ variable

instance FreshVariable Variable where
    infVariable variable = variable { variableCounter = Nothing }

    supVariable variable = variable { variableCounter = Just Sup }

    nextVariable variable@Variable { variableName, variableCounter } =
        variable
            { variableName = variableName'
            , variableCounter = variableCounter'
            }
      where
        variableName' = variableName { idLocation = AstLocationGeneratedVariable }
        variableCounter' =
            case variableCounter of
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

{- | Rename one set of variables while avoiding another.

If any of the variables to rename occurs in the set of avoided variables, it
will be mapped to a fresh name in the result. Every fresh name in the result
will also be unique among the fresh names.

To use @refreshVariables@ with 'Kore.Internal.Pattern.substitute', map the
result with 'Kore.Internal.TermLike.mkVar':

@
'Kore.Internal.TermLike.substitute'
    ('Kore.Internal.TermLike.mkVar' \<$\> refreshVariables avoid rename)
    :: 'Kore.Internal.TermLike TermLike' Variable
    -> 'Kore.Internal.TermLike TermLike' Variable
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
