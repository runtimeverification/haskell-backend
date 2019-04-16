{- |
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
 -}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , refreshVariables
    , nextVariable
    ) where

import qualified Data.Foldable as Foldable
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Data.Sup
import Kore.AST.Common
       ( Variable (..), illegalVariableCounter )
import Kore.AST.Identifier
import Kore.AST.MetaOrObject

{- | A 'FreshVariable' can be freshened, given a 'Natural' counter.
-}
class (forall level. Ord (variable level)) => FreshVariable variable where
    {- | Refresh a variable, renaming it avoid the given set.

    If the given variable occurs in the set, @refreshVariable@ must return
    'Just' a fresh variable which does not occur in the set. If the given
    variable does /not/ occur in the set, @refreshVariable@ /may/ return
    'Nothing'.

     -}
    refreshVariable
        :: MetaOrObject level
        => Set (variable level)
        -> variable level
        -> Maybe (variable level)

instance FreshVariable Variable where
    refreshVariable avoiding variable = do
        largest <- Set.lookupLT pivotMax avoiding
        if largest >= pivotMin
            then Just (fixSort . nextVariable $ largest)
            else Nothing
      where
        pivotMax = variable { variableCounter = Just Sup }
        pivotMin = variable { variableCounter = Nothing }
        fixSort var = var { variableSort = variableSort variable }

{- | Rename one set of variables while avoiding another.

If any of the variables to rename occurs in the set of avoided variables, it
will be mapped to a fresh name in the result. Every fresh name in the result
will also be unique among the fresh names.

To use @refreshVariables@ with 'Kore.Step.Pattern.substitute', map the result
with 'Kore.AST.Valid.mkVar':

@
'Kore.Step.Pattern.substitute' ('Kore.AST.Valid.mkVar' \<$\> refreshVariables avoid rename) :: 'Kore.Step.Pattern.StepPattern' Object Variable -> 'Kore.Step.Pattern.StepPattern' Object Variable
@

 -}
refreshVariables
    :: FreshVariable variable
    => Set (variable Object)  -- ^ variables to avoid
    -> Set (variable Object)  -- ^ variables to rename
    -> Map (variable Object) (variable Object)
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
nextVariable :: Variable level -> Variable level
nextVariable variable@Variable { variableName, variableCounter } =
    variable
        { variableName = variableName'
        , variableCounter = variableCounter'
        }
  where
    variableName' =
        variableName
            { idLocation = AstLocationGeneratedVariable }
    variableCounter' =
        case variableCounter of
            Nothing -> Just (Element 0)
            Just (Element a) -> Just (Element (succ a))
            Just Sup -> illegalVariableCounter
