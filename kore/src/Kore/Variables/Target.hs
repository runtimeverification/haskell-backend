{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Target specific variables for unification.

 -}

module Kore.Variables.Target
    ( Target (..)
    , unwrapVariable
    , isTarget
    , isNonTarget
    ) where

import           Data.Hashable
                 ( Hashable )
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import Kore.AST.Common
       ( SortedVariable (..) )
import Kore.Unparser
       ( Unparse (..) )
import Kore.Variables.Fresh
       ( FreshVariable (..) )

{- | Distinguish variables by their source.

'Target' variables always compare 'LT' 'NonTarget' variables, so that the
unification procedure prefers to generate substitutions for 'Target' variables
instead of 'NonTarget' variables.

 -}
data Target variable level
    = Target !(variable level)
    | NonTarget !(variable level)
    deriving (Eq, Generic, Show)

instance Ord (variable level) => Ord (Target variable level) where
    compare (Target var1) (Target var2) = compare var1 var2
    compare (Target _) (NonTarget _) = LT
    compare (NonTarget var1) (NonTarget var2) = compare var1 var2
    compare (NonTarget _) (Target _) = GT

instance Hashable (variable level) => Hashable (Target variable level)

unwrapVariable :: Target variable level -> variable level
unwrapVariable (Target variable) = variable
unwrapVariable (NonTarget variable) = variable

isTarget :: Target variable level -> Bool
isTarget (Target _) = True
isTarget (NonTarget _) = False

isNonTarget :: Target variable level -> Bool
isNonTarget = not . isTarget

instance
    SortedVariable variable
    => SortedVariable (Target variable)
  where
    sortedVariableSort (Target variable) = sortedVariableSort variable
    sortedVariableSort (NonTarget variable) = sortedVariableSort variable
    fromVariable = Target . fromVariable
    toVariable (Target var) = toVariable var
    toVariable (NonTarget var) = toVariable var

{- | Ensures that fresh variables are unique under 'unwrapStepperVariable'.
 -}
instance FreshVariable variable => FreshVariable (Target variable) where
    refreshVariable (Set.map unwrapVariable -> avoiding) =
        \case
            Target variable ->
                Target <$> refreshVariable avoiding variable
            NonTarget variable ->
                NonTarget <$> refreshVariable avoiding variable

instance
    Unparse (variable level) =>
    Unparse (Target variable level)
  where
    unparse (Target var) = unparse var
    unparse (NonTarget var) = unparse var
