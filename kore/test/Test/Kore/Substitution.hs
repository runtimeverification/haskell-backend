module Test.Kore.Substitution where

import           Kore.AST.Kore
import qualified Kore.Domain.Builtin as Domain

import Test.Kore

objectSort :: Sort Object
objectSort = SortVariableSort (SortVariable (testId "s"))

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = testId "v"
    , variableSort = objectSort
    , variableCounter = mempty
    }

unifiedObjectVariable :: Unified Variable
unifiedObjectVariable = UnifiedObject objectVariable

objectVariablePattern
    :: Pattern Object Domain.Builtin Variable CommonKorePattern
objectVariablePattern = VariablePattern objectVariable

objectVariableUnifiedPattern :: CommonKorePattern
objectVariableUnifiedPattern = asCommonKorePattern objectVariablePattern

metaSort :: Sort Meta
metaSort = SortVariableSort (SortVariable (testId "#s"))

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = testId "#v"
    , variableSort = metaSort
    , variableCounter = mempty
    }

unifiedMetaVariable :: Unified Variable
unifiedMetaVariable = UnifiedMeta metaVariable

metaVariablePattern :: Pattern Meta Domain.Builtin Variable CommonKorePattern
metaVariablePattern = VariablePattern metaVariable

metaVariableUnifiedPattern :: CommonKorePattern
metaVariableUnifiedPattern = asCommonKorePattern metaVariablePattern

objectTopPattern :: CommonKorePattern
objectTopPattern = asCommonKorePattern $ TopPattern $ Top objectSort

objectBottomPattern :: CommonKorePattern
objectBottomPattern = asCommonKorePattern $ BottomPattern $ Bottom objectSort
