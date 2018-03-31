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

unifiedObjectVariable :: UnifiedVariable Variable
unifiedObjectVariable = ObjectVariable objectVariable

objectVariablePattern :: Pattern Object Variable CommonKorePattern
objectVariablePattern = VariablePattern objectVariable

objectVariableUnifiedPattern :: CommonKorePattern
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

metaVariablePattern :: Pattern Meta Variable CommonKorePattern
metaVariablePattern = VariablePattern metaVariable

metaVariableUnifiedPattern :: CommonKorePattern
metaVariableUnifiedPattern = MetaPattern metaVariablePattern

objectTopPattern :: CommonKorePattern
objectTopPattern = ObjectPattern $ TopPattern $ Top objectSort

objectBottomPattern :: CommonKorePattern
objectBottomPattern = ObjectPattern $ BottomPattern $ Bottom objectSort
