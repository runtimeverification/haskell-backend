{-# Options -Wno-partial-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2022
License     : BSD-3-Clause
-}
module Booster.Syntax.Json.Base (
    -- export everything for debugging and testing only
    module Booster.Syntax.Json.Base,
    module Kore.Syntax.Json.Types,
) where

import Data.Foldable ()
import Kore.Syntax.Json.Types

------------------------------------------------------------

retractVariable :: KorePattern -> Maybe Id
retractVariable KJEVar{name} = Just name
retractVariable KJSVar{name} = Just name
retractVariable _ = Nothing

retractSortVariable :: Sort -> Maybe Id
retractSortVariable SortVar{name} = Just name
retractSortVariable _ = Nothing
