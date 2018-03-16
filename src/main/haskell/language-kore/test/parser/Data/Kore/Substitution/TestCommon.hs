{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.TestCommon where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore

objectSort :: Sort Object
objectSort = SortVariableSort (SortVariable (Id "s"))

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = Id "v"
    , variableSort = objectSort
    }

unifiedObjectVariable :: Unified Variable
unifiedObjectVariable = UnifiedObject objectVariable

objectVariablePattern :: Pattern Object Variable KorePattern
objectVariablePattern = VariablePattern objectVariable

objectVariableUnifiedPattern :: KorePattern
objectVariableUnifiedPattern = asObjectPattern objectVariablePattern

metaSort :: Sort Meta
metaSort = SortVariableSort (SortVariable (Id "#s"))

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = Id "#v"
    , variableSort = metaSort
    }

unifiedMetaVariable :: Unified Variable
unifiedMetaVariable = UnifiedMeta metaVariable

metaVariablePattern :: Pattern Meta Variable KorePattern
metaVariablePattern = VariablePattern metaVariable

metaVariableUnifiedPattern :: KorePattern
metaVariableUnifiedPattern = asMetaPattern metaVariablePattern

objectTopPattern :: KorePattern
objectTopPattern = asObjectPattern $ TopPattern $ Top objectSort

objectBottomPattern :: KorePattern
objectBottomPattern = asObjectPattern $ BottomPattern $ Bottom objectSort
