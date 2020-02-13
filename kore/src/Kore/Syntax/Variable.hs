{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE EmptyDataDeriving #-}

module Kore.Syntax.Variable
    ( Variable (..)
    , isOriginalVariable
    , illegalVariableCounter
    , externalizeFreshVariable
    , VariableName
    , toVariable
    , fromVariable
    , SortedVariable (..)
    , unparse2SortedVariable
    , Concrete
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural

import Data.Sup
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'Variable' corresponds to the @variable@ syntactic category from the
Semantics of K, Section 9.1.4 (Patterns).

Particularly, this is the type of variable in patterns returned by the parser.

-}
-- Invariant [variableCounter = Just Sup]:
-- No function returns a value that would match the pattern:
--
-- > Variable { variableCounter = Just Sup }
--
-- This value of variableCounter may only be used in refreshVariable to pivot
-- the set of variables that must not be captured.
data Variable = Variable
    { variableName :: !Id
    , variableCounter :: !(Maybe (Sup Natural))
    , variableSort :: !Sort
    }
    deriving (GHC.Generic, Show)

-- TODO (thomas.tuegel): Move variableSort out of Variable entirely, so that
-- only the identifiers remain.

instance Eq Variable where
    (==) a b =
            on (==) variableName a b
        &&  on (==) variableCounter a b
    {-# INLINE (==) #-}

{- | 'Variable' is uniquely identified by 'variableName' and 'variableCounter'.

Two 'Variable's with the same 'variableName' and 'variableCounter' but different
'variableSort's are not different so much as they are /inconsistent/.

 -}
instance Ord Variable where
    compare a b =
            on compare variableName a b
        <>  on compare variableCounter a b
    {-# INLINE compare #-}

instance Hashable Variable where
    hashWithSalt salt Variable { variableName, variableCounter } =
        salt `hashWithSalt` variableName `hashWithSalt` variableCounter
    {-# INLINE hashWithSalt #-}

instance NFData Variable

instance SOP.Generic Variable

instance SOP.HasDatatypeInfo Variable

instance Debug Variable

instance Diff Variable

instance Unparse Variable where
    unparse Variable { variableName, variableCounter, variableSort } =
        unparse variableName
        <> Pretty.pretty variableCounter
        <> Pretty.colon
        <> unparse variableSort

    unparse2 Variable { variableName, variableCounter } =
        unparse2 variableName
        <> Pretty.pretty variableCounter

instance From Variable Variable where
    from = id
    {-# INLINE from #-}

instance VariableName Variable

{- | Is the variable original (as opposed to generated)?
 -}
isOriginalVariable :: Variable -> Bool
isOriginalVariable Variable { variableCounter } = isNothing variableCounter

{- | Error thrown when 'variableCounter' takes an illegal value.
 -}
illegalVariableCounter :: a
illegalVariableCounter =
    error "Illegal use of Variable { variableCounter = Just Sup }"

{- | Reset 'variableCounter' so that a 'Variable' may be unparsed.

@externalizeFreshVariable@ is not injective and is unsafe if used with
'mapVariables'. See 'Kore.Internal.Pattern.externalizeFreshVariables' instead.

 -}
externalizeFreshVariable :: Variable -> Variable
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

{- | 'VariableName' is the name of a Kore variable.

A 'VariableName' has instances:

* @'From' variable 'Variable'@
* @'From' 'Variable' variable@

such that both implementations of 'from' are injective,

prop> (==) (fromVariable x) (fromVariable y) === (==) x y

prop> (==) x y === (==) (toVariable x) (toVariable y)

 -}
class
    (Ord variable, From variable Variable, From Variable variable)
    => VariableName variable

-- | An injection from 'Variable' to any 'VariableName'.
fromVariable :: forall variable. VariableName variable => Variable -> variable
fromVariable = from @Variable @variable

-- | An injection from any 'VariableName' to 'Variable'.
toVariable :: forall variable. VariableName variable => variable -> Variable
toVariable = from @variable @Variable

{- | 'SortedVariable' is a Kore variable with a known sort.

 -}
class SortedVariable variable where
    -- | The known 'Sort' of the given variable.
    sortedVariableSort :: variable -> Sort

instance SortedVariable Variable where
    sortedVariableSort = variableSort

{- | Unparse any 'SortedVariable' in an Applicative Kore binder.

Variables occur without their sorts as subterms in Applicative Kore patterns,
but with their sorts in binders like @\\exists@ and
@\\forall@. @unparse2SortedVariable@ adds the sort ascription to the unparsed
variable for the latter case.

 -}
unparse2SortedVariable
    :: (SortedVariable variable, Unparse variable)
    => variable
    -> Pretty.Doc ann
unparse2SortedVariable variable =
    unparse2 variable <> Pretty.colon <> unparse (sortedVariableSort variable)

{- | @Concrete@ is a variable occuring in a concrete pattern.

Concrete patterns do not contain variables, so this is an uninhabited type
(it has no constructors).

See also: 'Data.Void.Void'

 -}
data Concrete
    deriving (Eq, GHC.Generic, Ord, Read, Show)

instance Hashable Concrete

instance NFData Concrete

instance SOP.Generic Concrete

instance SOP.HasDatatypeInfo Concrete

instance Debug Concrete

instance Diff Concrete

instance Unparse Concrete where
    unparse = \case {}
    unparse2 = \case {}

instance SortedVariable Concrete where
    sortedVariableSort = \case {}

instance VariableName Concrete

instance From Variable Concrete where
    from = error "Cannot construct a variable in a concrete term!"
    {-# INLINE from #-}

instance From Concrete Variable where
    from = \case {}
    {-# INLINE from #-}
