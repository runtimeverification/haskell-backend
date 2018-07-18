{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Test.Data.Kore.Substitution where

import           Test.Data.Kore

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject

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
