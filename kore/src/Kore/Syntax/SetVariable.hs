{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.SetVariable
    ( SetVariable
    , mkSetVariable
    ) where

import Kore.Sort
import Kore.Syntax.Variable

-- | Applicative-Kore set variables
type SetVariable variable = Variable1 (SetVariableName variable)

mkSetVariable :: Id -> Sort -> SetVariable VariableName
mkSetVariable base variableSort1 =
    Variable1
    { variableName1 = SetVariableName (mkVariableName base)
    , variableSort1
    }
