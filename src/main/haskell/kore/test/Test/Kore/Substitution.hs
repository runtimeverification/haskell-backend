module Test.Kore.Substitution where

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject

import Test.Kore

objectSort :: Sort Object
objectSort = SortVariableSort (SortVariable (testId "s"))

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = testId "v"
    , variableSort = objectSort
    }

unifiedObjectVariable :: Unified Variable
unifiedObjectVariable = UnifiedObject objectVariable

objectVariablePattern :: Pattern Object Variable CommonKorePattern
objectVariablePattern = VariablePattern objectVariable

objectVariableUnifiedPattern :: CommonKorePattern
objectVariableUnifiedPattern = asKorePattern objectVariablePattern

metaSort :: Sort Meta
metaSort = SortVariableSort (SortVariable (testId "#s"))

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = testId "#v"
    , variableSort = metaSort
    }

unifiedMetaVariable :: Unified Variable
unifiedMetaVariable = UnifiedMeta metaVariable

metaVariablePattern :: Pattern Meta Variable CommonKorePattern
metaVariablePattern = VariablePattern metaVariable

metaVariableUnifiedPattern :: CommonKorePattern
metaVariableUnifiedPattern = asKorePattern metaVariablePattern

objectTopPattern :: CommonKorePattern
objectTopPattern = asKorePattern $ TopPattern $ Top objectSort

objectBottomPattern :: CommonKorePattern
objectBottomPattern = asKorePattern $ BottomPattern $ Bottom objectSort
