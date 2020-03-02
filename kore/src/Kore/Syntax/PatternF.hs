{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.PatternF
    ( PatternF (..)
    , mapVariables
    , traverseVariables
    -- * Pure pattern heads
    , groundHead
    , constant
    -- * Re-exports
    , Const (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Functor.Const
import Data.Functor.Identity
    ( Identity (..)
    )
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Sort
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.DomainValue
import Kore.Syntax.ElementVariable
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Inhabitant
import Kore.Syntax.Mu
import Kore.Syntax.Next
import Kore.Syntax.Not
import Kore.Syntax.Nu
import Kore.Syntax.Or
import Kore.Syntax.Rewrites
import Kore.Syntax.SetVariable
import Kore.Syntax.StringLiteral
import Kore.Syntax.Top
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.UnifiedVariable

{- | 'PatternF' is the 'Base' functor of Kore patterns

-}
data PatternF variable child
    = AndF           !(And Sort child)
    | ApplicationF   !(Application SymbolOrAlias child)
    | BottomF        !(Bottom Sort child)
    | CeilF          !(Ceil Sort child)
    | DomainValueF   !(DomainValue Sort child)
    | EqualsF        !(Equals Sort child)
    | ExistsF        !(Exists Sort variable child)
    | FloorF         !(Floor Sort child)
    | ForallF        !(Forall Sort variable child)
    | IffF           !(Iff Sort child)
    | ImpliesF       !(Implies Sort child)
    | InF            !(In Sort child)
    | MuF            !(Mu variable child)
    | NextF          !(Next Sort child)
    | NotF           !(Not Sort child)
    | NuF            !(Nu variable child)
    | OrF            !(Or Sort child)
    | RewritesF      !(Rewrites Sort child)
    | TopF           !(Top Sort child)
    | InhabitantF    !(Inhabitant child)
    | StringLiteralF !(Const StringLiteral child)
    | VariableF      !(Const (UnifiedVariable variable) child)
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (PatternF variable child)

instance SOP.HasDatatypeInfo (PatternF variable child)

instance (Debug variable, Debug child) => Debug (PatternF variable child)

instance
    ( Debug variable, Debug child, Diff variable, Diff child )
    => Diff (PatternF variable child)

instance
    (Hashable child, Hashable variable) =>
    Hashable (PatternF variable child)

instance (NFData child, NFData variable) => NFData (PatternF variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (PatternF variable child)
  where
    unparse = unparseGeneric
    unparse2 = unparse2Generic

{- | Use the provided mapping to replace all variables in a 'PatternF' head.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

-}
mapVariables
    :: (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> PatternF variable1 child
    -> PatternF variable2 child
mapVariables mapElemVar mapSetVar =
    runIdentity
    . traverseVariables (Identity . mapElemVar) (Identity . mapSetVar)
{-# INLINE mapVariables #-}

{- | Use the provided traversal to replace all variables in a 'PatternF' head.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

-}
traverseVariables
    :: Applicative f
    => (ElementVariable variable1 -> f (ElementVariable variable2))
    -> (SetVariable variable1 -> f (SetVariable variable2))
    -> PatternF variable1 child
    -> f (PatternF variable2 child)
traverseVariables trElemVar trSetVar =
    \case
        -- Non-trivial cases
        ExistsF any0 -> ExistsF <$> traverseVariablesExists any0
        ForallF all0 -> ForallF <$> traverseVariablesForall all0
        MuF any0 -> MuF <$> traverseVariablesMu any0
        NuF any0 -> NuF <$> traverseVariablesNu any0
        VariableF variableF -> traverseVariable variableF
        -- Trivial cases
        AndF andP -> pure (AndF andP)
        ApplicationF appP -> pure (ApplicationF appP)
        BottomF botP -> pure (BottomF botP)
        CeilF ceilP -> pure (CeilF ceilP)
        DomainValueF dvP -> pure (DomainValueF dvP)
        EqualsF eqP -> pure (EqualsF eqP)
        FloorF flrP -> pure (FloorF flrP)
        IffF iffP -> pure (IffF iffP)
        ImpliesF impP -> pure (ImpliesF impP)
        InF inP -> pure (InF inP)
        NextF nxtP -> pure (NextF nxtP)
        NotF notP -> pure (NotF notP)
        OrF orP -> pure (OrF orP)
        RewritesF rewP -> pure (RewritesF rewP)
        StringLiteralF strP -> pure (StringLiteralF strP)
        TopF topP -> pure (TopF topP)
        InhabitantF s -> pure (InhabitantF s)
  where
    traverseVariable (Const variable) =
        VariableF . Const
        <$> traverseUnifiedVariable trElemVar trSetVar variable
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort
        <$> trElemVar existsVariable
        <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort
        <$> trElemVar forallVariable
        <*> pure forallChild
    traverseVariablesMu Mu { muVariable, muChild } =
        Mu <$> trSetVar muVariable <*> pure muChild
    traverseVariablesNu Nu { nuVariable, nuChild } =
        Nu <$> trSetVar nuVariable <*> pure nuChild

-- | Given an 'Id', 'groundHead' produces the head of an 'Application'
-- corresponding to that argument.
groundHead :: Text -> AstLocation -> SymbolOrAlias
groundHead ctor location = SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = ctor
        , idLocation = location
        }
    , symbolOrAliasParams = []
    }

-- | Given a head and a list of children, produces an 'ApplicationF'
--  applying the given head to the children
apply :: SymbolOrAlias -> [child] -> PatternF variable child
apply patternHead patterns = ApplicationF Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

-- |Applies the given head to the empty list of children to obtain a
-- constant 'ApplicationF'
constant :: SymbolOrAlias -> PatternF variable child
constant patternHead = apply patternHead []
