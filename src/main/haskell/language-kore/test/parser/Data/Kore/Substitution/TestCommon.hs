{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.TestCommon where

import           Data.Kore.Substitution.Class

import           Data.Kore.AST

objectSort :: Sort Object
objectSort = SortVariableSort (SortVariable (Id "s"))

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = Id "v"
    , variableSort = objectSort
    }

unifiedObjectVariable :: UnifiedVariable Variable
unifiedObjectVariable = ObjectVariable objectVariable

objectVariablePattern :: Pattern Object Variable UnifiedPattern
objectVariablePattern = VariablePattern objectVariable

objectVariableUnifiedPattern :: UnifiedPattern
objectVariableUnifiedPattern = ObjectPattern objectVariablePattern

metaSort :: Sort Meta
metaSort = SortVariableSort (SortVariable (Id "#s"))

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = Id "#v"
    , variableSort = metaSort
    }

unifiedMetaVariable :: UnifiedVariable Variable
unifiedMetaVariable = MetaVariable metaVariable

metaVariablePattern :: Pattern Meta Variable UnifiedPattern
metaVariablePattern = VariablePattern metaVariable

metaVariableUnifiedPattern :: UnifiedPattern
metaVariableUnifiedPattern = MetaPattern metaVariablePattern

objectTopPattern :: UnifiedPattern
objectTopPattern = ObjectPattern $ TopPattern $ Top objectSort

objectBottomPattern :: UnifiedPattern
objectBottomPattern = ObjectPattern $ BottomPattern $ Bottom objectSort
