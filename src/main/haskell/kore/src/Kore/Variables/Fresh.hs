{-|
Module      : Kore.Variables.Fresh
Description : Specify an interface for generating fresh variables
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

The syntax of a variable generated from a regular one is
var_<original-variable-name>_<disambiguating-number>
As an example, a variable generated from "v" could be called "var_v_10". Note
that a variable generated from "var_v_10" would NOT be called "var_var_v_10_11",
it would use the same original variable name "v", so it would look something
like "var_v_11".

-}
module Kore.Variables.Fresh
    ( FreshVariable (..)
    , nextVariable
    ) where

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
