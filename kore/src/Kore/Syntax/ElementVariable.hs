{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.ElementVariable
    ( ElementVariable
    , mkElementVariable
    ) where

import Kore.Sort
import Kore.Syntax.Variable

-- | Element (singleton) Kore variables
type ElementVariable variable = Variable1 (ElementVariableName variable)

mkElementVariable :: Id -> Sort -> ElementVariable VariableName
mkElementVariable base variableSort1 =
    Variable1
    { variableName1 = ElementVariableName (mkVariableName base)
    , variableSort1
    }
