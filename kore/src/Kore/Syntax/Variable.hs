{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Variable
    ( Variable (..)
    , isOriginalVariable
    , illegalVariableCounter
    , externalizeFreshVariable
    , SortedVariable (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
import           Data.Maybe
                 ( isNothing )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )
import           Numeric.Natural

import Data.Sup
import Kore.Sort
import Kore.Unparser

{-|'Variable' corresponds to the @object-variable@ and
@meta-variable@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

Particularly, this is the type of variable in patterns returned by the parser.

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
-- Invariant [variableCounter = Just Sup]:
-- No function returns a value that would match the pattern:
--
-- > Variable { variableCounter = Just Sup }
--
-- This value of variableCounter may only be used in refreshVariable to pivot
-- the set of variables that must not be captured.
data Variable level = Variable
    { variableName :: !Id
    , variableCounter :: !(Maybe (Sup Natural))
    , variableSort :: !Sort
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Variable level)

instance NFData (Variable level)

instance Unparse (Variable level) where
    unparse Variable { variableName, variableCounter, variableSort } =
        unparse variableName
        <> Pretty.pretty variableCounter
        <> Pretty.colon
        <> unparse variableSort
    unparse2 Variable { variableName, variableCounter } =
        unparseIdLower variableName
        <> Pretty.pretty variableCounter
    unparse2BindingVariables Variable { variableName, variableCounter, variableSort } =
        unparseIdLower variableName
        <> Pretty.pretty variableCounter
        <> Pretty.colon
        <> unparse2 variableSort

{- | Is the variable original (as opposed to generated)?
 -}
isOriginalVariable :: Variable level -> Bool
isOriginalVariable Variable { variableCounter } = isNothing variableCounter

{- | Error thrown when 'variableCounter' takes an illegal value.
 -}
illegalVariableCounter :: a
illegalVariableCounter =
    error "Illegal use of Variable { variableCounter = Just Sup }"

{- | Reset 'variableCounter' so that a 'Variable' may be unparsed.

@externalizeFreshVariable@ is not injective and is unsafe if used with
'mapVariables'. See 'Kore.Step.Pattern.externalizeFreshVariables' instead.

 -}
externalizeFreshVariable :: Variable level -> Variable level
externalizeFreshVariable variable@Variable { variableName, variableCounter } =
    variable
        { variableName = variableName'
        , variableCounter = Nothing
        }
  where
    variableName' =
        variableName
            { getId =
                case variableCounter of
                    Nothing -> getId variableName
                    Just (Element n) -> getId variableName <> Text.pack (show n)
                    Just Sup -> illegalVariableCounter
            , idLocation = AstLocationGeneratedVariable
            }

{- | 'SortedVariable' is a Kore variable with a known sort.

The instances of @SortedVariable@ must encompass the 'Variable' type by
implementing 'fromVariable', i.e. we must be able to construct a
@SortedVariable@ given a parsed 'Variable'.

'toVariable' may delete information so that

> toVariable . fromVariable === id :: Variable level -> Variable level

but the reverse is not required.

 -}
class SortedVariable (variable :: * -> *) where
    -- | The known 'Sort' of the given variable.
    sortedVariableSort :: variable level -> Sort
    sortedVariableSort variable =
        variableSort
      where
        Variable { variableSort } = toVariable variable

    -- | Convert a variable from the parsed syntax of Kore.
    fromVariable :: Variable level -> variable level
    -- | Extract the parsed syntax of a Kore variable.
    toVariable :: variable level -> Variable level

instance SortedVariable Variable where
    sortedVariableSort = variableSort
    fromVariable = id
    toVariable = id
