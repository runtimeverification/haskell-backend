module Test.Kore.Substitution where

import qualified Kore.Domain.Builtin as Domain
import           Kore.Syntax

import Test.Kore

objectSort :: Sort
objectSort = SortVariableSort (SortVariable (testId "s"))

objectVariable :: Variable
objectVariable = Variable
    { variableName = testId "v"
    , variableSort = objectSort
    , variableCounter = mempty
    }

objectVariablePattern
    :: PatternF Domain.Builtin Variable ParsedPattern
objectVariablePattern = VariableF objectVariable

objectVariableUnifiedPattern :: ParsedPattern
objectVariableUnifiedPattern = asParsedPattern objectVariablePattern

metaSort :: Sort
metaSort = SortVariableSort (SortVariable (testId "#s"))

metaVariable :: Variable
metaVariable = Variable
    { variableName = testId "#v"
    , variableSort = metaSort
    , variableCounter = mempty
    }

metaVariablePattern :: PatternF Domain.Builtin Variable ParsedPattern
metaVariablePattern = VariableF metaVariable

metaVariableUnifiedPattern :: ParsedPattern
metaVariableUnifiedPattern = asParsedPattern metaVariablePattern

objectTopPattern :: ParsedPattern
objectTopPattern = asParsedPattern $ TopF $ Top objectSort

objectBottomPattern :: ParsedPattern
objectBottomPattern = asParsedPattern $ BottomF $ Bottom objectSort
