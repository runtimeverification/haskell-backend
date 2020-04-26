{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Rewriting.RewritingVariable
    ( RewritingVariable (..)
    , unwrapConfiguration
    , isConfigVariable
    ) where

import Prelude.Kore

import Data.Generics.Wrapped
    ( _Unwrapped
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Unparser
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( foldMapVariable
    )

newtype RewritingVariable =
    RewritingVariable { getRewritingVariable :: Target Variable }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving newtype FreshPartialOrd
    deriving newtype VariableName
    deriving newtype SubstitutionOrd
    deriving newtype Unparse

instance Hashable RewritingVariable

instance SOP.Generic RewritingVariable

instance SOP.HasDatatypeInfo RewritingVariable

instance Debug RewritingVariable

instance Diff RewritingVariable

instance From RewritingVariable Variable where
    from = from @_ @Variable . getRewritingVariable

instance From Variable RewritingVariable where
    from = RewritingVariable . from @Variable

instance SortedVariable RewritingVariable where
    lensVariableSort = _Unwrapped . lensVariableSort

instance FreshVariable RewritingVariable

getElementRewritingVariable
    :: ElementVariable RewritingVariable -> ElementVariable Variable
getElementRewritingVariable =
    Target.unTargetElement . fmap getRewritingVariable

getSetRewritingVariable
    :: SetVariable RewritingVariable -> SetVariable Variable
getSetRewritingVariable =
    Target.unTargetSet . fmap getRewritingVariable

getPatternRewritingVariable
    :: Pattern RewritingVariable
    -> Pattern Variable
getPatternRewritingVariable =
    Pattern.mapVariables
        getElementRewritingVariable
        getSetRewritingVariable

isConfigVariable :: RewritingVariable -> Bool
isConfigVariable = Target.isNonTarget . getRewritingVariable

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
unwrapConfiguration :: Pattern RewritingVariable -> Pattern Variable
unwrapConfiguration config@Conditional { substitution } =
    getPatternRewritingVariable
        config { Pattern.substitution = substitution' }
  where
    substitution' =
        Substitution.filter
            (foldMapVariable isConfigVariable)
            substitution
