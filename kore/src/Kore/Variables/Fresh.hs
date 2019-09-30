{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , Renaming
    , refreshVariables
    , nextVariable
    -- * Re-exports
    , module Kore.Syntax.Variable
    ) where

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


type Renaming variable =
    Map (UnifiedVariable variable) (UnifiedVariable variable)

instance FreshVariable variable => FreshVariable (ElementVariable variable)
  where
    refreshVariable avoid = traverse (refreshVariable avoid')
      where
        avoid' = Set.map getElementVariable avoid

instance FreshVariable variable => FreshVariable (SetVariable variable)
  where
    refreshVariable avoid = traverse (refreshVariable avoid')
      where
        avoid' = Set.map getSetVariable avoid

instance FreshVariable variable => FreshVariable (UnifiedVariable variable)
  where
    refreshVariable avoid = \case
        SetVar v -> SetVar <$> refreshVariable setVars v
        ElemVar v -> ElemVar <$> refreshVariable elemVars v
      where
        avoid' = Set.toList avoid
        setVars = Set.fromList [v | SetVar v <- avoid']
        elemVars = Set.fromList [v | ElemVar v <- avoid']

instance FreshVariable Variable where
    refreshVariable avoiding variable = do
        fixedLargest <- fixSort <$> Set.lookupLT pivotMax avoiding
        if fixedLargest >= pivotMin
            then Just (nextVariable fixedLargest)
            else Nothing
      where
        pivotMax = variable { variableCounter = Just Sup }
        pivotMin = variable { variableCounter = Nothing }
        fixSort var = var { variableSort = variableSort variable }

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

{- | Increase the 'variableCounter' of a 'Variable'
 -}
nextVariable :: Variable -> Variable
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
