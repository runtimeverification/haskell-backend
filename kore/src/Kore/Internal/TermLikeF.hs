{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.TermLikeF
    ( TermLikeF (..)
    , Evaluated (..)
    , mapVariablesF
    , traverseVariablesF
    -- * Re-exports
    , Symbol (..)
    , Alias (..)
    , SortedVariable (..)
    , module Kore.Syntax.Id
    , CofreeF (..), Comonad (..)
    , Sort (..), SortActual (..), SortVariable (..)
    , charMetaSort, stringMetaSort
    , module Kore.Syntax.And
    , module Kore.Syntax.Application
    , module Kore.Syntax.Bottom
    , module Kore.Syntax.Ceil
    , module Kore.Syntax.CharLiteral
    , module Kore.Syntax.DomainValue
    , module Kore.Syntax.Equals
    , module Kore.Syntax.Exists
    , module Kore.Syntax.Floor
    , module Kore.Syntax.Forall
    , module Kore.Syntax.Iff
    , module Kore.Syntax.Implies
    , module Kore.Syntax.In
    , module Kore.Syntax.Mu
    , module Kore.Syntax.Next
    , module Kore.Syntax.Not
    , module Kore.Syntax.Nu
    , module Kore.Syntax.Or
    , module Kore.Syntax.Rewrites
    , module Kore.Syntax.SetVariable
    , module Kore.Syntax.StringLiteral
    , module Kore.Syntax.Top
    , module Variable
    ) where


import           Control.Applicative
import           Control.Comonad
import           Control.Comonad.Trans.Cofree
import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Foldable as Foldable
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Pattern.Defined as Pattern
import           Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.Function as Pattern
import qualified Kore.Attribute.Pattern.Functional as Pattern
import           Kore.Attribute.Synthetic
import           Kore.Domain.Builtin
import           Kore.Internal.Alias
import           Kore.Internal.Symbol
import           Kore.Sort
import           Kore.Syntax.And
import           Kore.Syntax.Application
import           Kore.Syntax.Bottom
import           Kore.Syntax.Ceil
import           Kore.Syntax.CharLiteral
import           Kore.Syntax.DomainValue
import           Kore.Syntax.Equals
import           Kore.Syntax.Exists
import           Kore.Syntax.Floor
import           Kore.Syntax.Forall
import           Kore.Syntax.Id
import           Kore.Syntax.Iff
import           Kore.Syntax.Implies
import           Kore.Syntax.In
import           Kore.Syntax.Mu
import           Kore.Syntax.Next
import           Kore.Syntax.Not
import           Kore.Syntax.Nu
import           Kore.Syntax.Or
import           Kore.Syntax.Rewrites
import           Kore.Syntax.SetVariable
import           Kore.Syntax.StringLiteral
import           Kore.Syntax.Top
import           Kore.Syntax.Variable as Variable
import           Kore.Unparser
                 ( Unparse (..) )
import qualified Kore.Unparser as Unparser


{- | @Evaluated@ wraps patterns which are fully evaluated.

Fully-evaluated patterns will not be simplified further because no progress
could be made.

 -}
newtype Evaluated child = Evaluated { getEvaluated :: child }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (Evaluated child)

instance SOP.HasDatatypeInfo (Evaluated child)

instance Hashable child => Hashable (Evaluated child)

instance NFData child => NFData (Evaluated child)

instance Unparse child => Unparse (Evaluated child) where
    unparse evaluated =
        Pretty.vsep ["/* evaluated: */", Unparser.unparseGeneric evaluated]
    unparse2 evaluated =
        Pretty.vsep ["/* evaluated: */", Unparser.unparse2Generic evaluated]

instance Synthetic Evaluated syn where
    synthetic = getEvaluated
    {-# INLINE synthetic #-}

{- | 'TermLikeF' is the 'Base' functor of internal term-like patterns.

-}
data TermLikeF key variable child
    = AndF           !(And Sort child)
    | ApplySymbolF   !(Application Symbol child)
    | ApplyAliasF    !(Application Alias child)
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
    | StringLiteralF !StringLiteral
    | CharLiteralF   !CharLiteral
    | TopF           !(Top Sort child)
    | VariableF      !variable
    | InhabitantF    !Sort
    | SetVariableF   !(SetVariable variable)
    | BuiltinF       !(Builtin key child)
    | EvaluatedF     !(Evaluated child)
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (TermLikeF key variable child)

instance SOP.HasDatatypeInfo (TermLikeF key variable child)

instance
    (Hashable child, Hashable key, Hashable variable) =>
    Hashable (TermLikeF key variable child)

instance
    (NFData child, NFData key, NFData variable) =>
    NFData (TermLikeF key variable child)

instance
    ( SortedVariable variable, Unparse variable
    , Unparse child, Unparse key
    ) =>
    Unparse (TermLikeF key variable child)
  where
    unparse = Unparser.unparseGeneric
    unparse2 = Unparser.unparse2Generic

instance
    Ord variable =>
    Synthetic (TermLikeF key variable) (FreeVariables variable)
  where
    -- TODO (thomas.tuegel): Use SOP.Generic here, after making the children
    -- Functors.
    synthetic (ForallF forallF) = synthetic forallF
    synthetic (ExistsF existsF) = synthetic existsF
    synthetic (VariableF variable) = freeVariable variable

    synthetic (AndF andF) = synthetic andF
    synthetic (ApplySymbolF applySymbolF) = synthetic applySymbolF
    synthetic (ApplyAliasF applyAliasF) = synthetic applyAliasF
    synthetic (BottomF bottomF) = synthetic bottomF
    synthetic (CeilF ceilF) = synthetic ceilF
    synthetic (DomainValueF domainValueF) = synthetic domainValueF
    synthetic (EqualsF equalsF) = synthetic equalsF
    synthetic (FloorF floorF) = synthetic floorF
    synthetic (IffF iffF) = synthetic iffF
    synthetic (ImpliesF impliesF) = synthetic impliesF
    synthetic (InF inF) = synthetic inF
    synthetic (NextF nextF) = synthetic nextF
    synthetic (NotF notF) = synthetic notF
    synthetic (OrF orF) = synthetic orF
    synthetic (RewritesF rewritesF) = synthetic rewritesF
    synthetic (TopF topF) = synthetic topF
    synthetic (BuiltinF builtinF) = Foldable.fold builtinF
    synthetic (EvaluatedF evaluatedF) = synthetic evaluatedF

    synthetic (StringLiteralF stringLiteral) = synthetic (Const stringLiteral)
    synthetic (CharLiteralF charLiteral) = synthetic (Const charLiteral)
    synthetic (InhabitantF _) = mempty

    -- TODO (thomas.tuegel): Track free set variables.
    synthetic (MuF muF) = synthetic muF
    synthetic (NuF nuF) = synthetic nuF
    synthetic (SetVariableF _) = mempty
    {-# INLINE synthetic #-}

instance
    SortedVariable variable =>
    Synthetic (TermLikeF key variable) Sort
  where
    -- TODO (thomas.tuegel): Use SOP.Generic here, after making the children
    -- Functors.
    synthetic (ForallF forallF) = synthetic forallF
    synthetic (ExistsF existsF) = synthetic existsF
    synthetic (VariableF variable) = sortedVariableSort variable

    synthetic (AndF andF) = synthetic andF
    synthetic (ApplySymbolF applySymbolF) = synthetic applySymbolF
    synthetic (ApplyAliasF applyAliasF) = synthetic applyAliasF
    synthetic (BottomF bottomF) = synthetic bottomF
    synthetic (CeilF ceilF) = synthetic ceilF
    synthetic (DomainValueF domainValueF) = synthetic domainValueF
    synthetic (EqualsF equalsF) = synthetic equalsF
    synthetic (FloorF floorF) = synthetic floorF
    synthetic (IffF iffF) = synthetic iffF
    synthetic (ImpliesF impliesF) = synthetic impliesF
    synthetic (InF inF) = synthetic inF
    synthetic (NextF nextF) = synthetic nextF
    synthetic (NotF notF) = synthetic notF
    synthetic (OrF orF) = synthetic orF
    synthetic (RewritesF rewritesF) = synthetic rewritesF
    synthetic (TopF topF) = synthetic topF
    synthetic (BuiltinF builtinF) = synthetic builtinF
    synthetic (EvaluatedF evaluatedF) = synthetic evaluatedF

    synthetic (StringLiteralF stringLiteral) = synthetic (Const stringLiteral)
    synthetic (CharLiteralF charLiteral) = synthetic (Const charLiteral)
    synthetic (InhabitantF inhSort) = synthetic (Const inhSort)

    synthetic (MuF muF) = synthetic muF
    synthetic (NuF nuF) = synthetic nuF
    synthetic (SetVariableF setVariable) =
        sortedVariableSort (getVariable setVariable)
    {-# INLINE synthetic #-}

instance Synthetic (TermLikeF key variable) Pattern.Functional where
    -- TODO (thomas.tuegel): Use SOP.Generic here, after making the children
    -- Functors.
    synthetic (ForallF forallF) = synthetic forallF
    synthetic (ExistsF existsF) = synthetic existsF
    synthetic (VariableF _) = Pattern.Functional True

    synthetic (AndF andF) = synthetic andF
    synthetic (ApplySymbolF applySymbolF) = synthetic applySymbolF
    synthetic (ApplyAliasF applyAliasF) = synthetic applyAliasF
    synthetic (BottomF bottomF) = synthetic bottomF
    synthetic (CeilF ceilF) = synthetic ceilF
    synthetic (DomainValueF domainValueF) = synthetic domainValueF
    synthetic (EqualsF equalsF) = synthetic equalsF
    synthetic (FloorF floorF) = synthetic floorF
    synthetic (IffF iffF) = synthetic iffF
    synthetic (ImpliesF impliesF) = synthetic impliesF
    synthetic (InF inF) = synthetic inF
    synthetic (NextF nextF) = synthetic nextF
    synthetic (NotF notF) = synthetic notF
    synthetic (OrF orF) = synthetic orF
    synthetic (RewritesF rewritesF) = synthetic rewritesF
    synthetic (TopF topF) = synthetic topF
    synthetic (BuiltinF builtinF) = synthetic builtinF
    synthetic (EvaluatedF evaluatedF) = synthetic evaluatedF

    synthetic (StringLiteralF stringLiteral) = synthetic (Const stringLiteral)
    synthetic (CharLiteralF charLiteral) = synthetic (Const charLiteral)
    synthetic (InhabitantF inhSort) = synthetic (Const inhSort)

    synthetic (MuF muF) = synthetic muF
    synthetic (NuF nuF) = synthetic nuF
    synthetic (SetVariableF _) = Pattern.Functional False
    {-# INLINE synthetic #-}

instance Synthetic (TermLikeF key variable) Pattern.Function where
    -- TODO (thomas.tuegel): Use SOP.Generic here, after making the children
    -- Functors.
    synthetic (ForallF forallF) = synthetic forallF
    synthetic (ExistsF existsF) = synthetic existsF
    synthetic (VariableF _) = Pattern.Function True

    synthetic (AndF andF) = synthetic andF
    synthetic (ApplySymbolF applySymbolF) = synthetic applySymbolF
    synthetic (ApplyAliasF applyAliasF) = synthetic applyAliasF
    synthetic (BottomF bottomF) = synthetic bottomF
    synthetic (CeilF ceilF) = synthetic ceilF
    synthetic (DomainValueF domainValueF) = synthetic domainValueF
    synthetic (EqualsF equalsF) = synthetic equalsF
    synthetic (FloorF floorF) = synthetic floorF
    synthetic (IffF iffF) = synthetic iffF
    synthetic (ImpliesF impliesF) = synthetic impliesF
    synthetic (InF inF) = synthetic inF
    synthetic (NextF nextF) = synthetic nextF
    synthetic (NotF notF) = synthetic notF
    synthetic (OrF orF) = synthetic orF
    synthetic (RewritesF rewritesF) = synthetic rewritesF
    synthetic (TopF topF) = synthetic topF
    synthetic (BuiltinF builtinF) = synthetic builtinF
    synthetic (EvaluatedF evaluatedF) = synthetic evaluatedF

    synthetic (StringLiteralF _) = Pattern.Function True
    synthetic (CharLiteralF _) = Pattern.Function True
    synthetic (InhabitantF _) = Pattern.Function False

    synthetic (MuF muF) = synthetic muF
    synthetic (NuF nuF) = synthetic nuF
    synthetic (SetVariableF _) = Pattern.Function False
    {-# INLINE synthetic #-}

instance Synthetic (TermLikeF key variable) Pattern.Defined where
    -- TODO (thomas.tuegel): Use SOP.Generic here, after making the children
    -- Functors.
    synthetic (ForallF forallF) = synthetic forallF
    synthetic (ExistsF existsF) = synthetic existsF
    synthetic (VariableF _) = Pattern.Defined True

    synthetic (AndF andF) = synthetic andF
    synthetic (ApplySymbolF applySymbolF) = synthetic applySymbolF
    synthetic (ApplyAliasF applyAliasF) = synthetic applyAliasF
    synthetic (BottomF bottomF) = synthetic bottomF
    synthetic (CeilF ceilF) = synthetic ceilF
    synthetic (DomainValueF domainValueF) = synthetic domainValueF
    synthetic (EqualsF equalsF) = synthetic equalsF
    synthetic (FloorF floorF) = synthetic floorF
    synthetic (IffF iffF) = synthetic iffF
    synthetic (ImpliesF impliesF) = synthetic impliesF
    synthetic (InF inF) = synthetic inF
    synthetic (NextF nextF) = synthetic nextF
    synthetic (NotF notF) = synthetic notF
    synthetic (OrF orF) = synthetic orF
    synthetic (RewritesF rewritesF) = synthetic rewritesF
    synthetic (TopF topF) = synthetic topF
    synthetic (BuiltinF builtinF) = synthetic builtinF
    synthetic (EvaluatedF evaluatedF) = synthetic evaluatedF

    synthetic (StringLiteralF _) = Pattern.Defined True
    synthetic (CharLiteralF _) = Pattern.Defined True
    synthetic (InhabitantF _) = Pattern.Defined True

    synthetic (MuF muF) = synthetic muF
    synthetic (NuF nuF) = synthetic nuF
    synthetic (SetVariableF _) = Pattern.Defined False
    {-# INLINE synthetic #-}

{- | Use the provided mapping to replace all variables in a 'TermLikeF' head.

__Warning__: @mapVariablesF@ will capture variables if the provided mapping is
not injective!

-}
mapVariablesF
    :: (variable1 -> variable2)
    -> TermLikeF key variable1 child
    -> TermLikeF key variable2 child
mapVariablesF mapping = runIdentity . traverseVariablesF (Identity . mapping)

{- | Use the provided traversal to replace all variables in a 'TermLikeF' head.

__Warning__: @traverseVariablesF@ will capture variables if the provided
traversal is not injective!

-}
traverseVariablesF
    :: Applicative f
    => (variable1 -> f variable2)
    ->    TermLikeF key variable1 child
    -> f (TermLikeF key variable2 child)
traverseVariablesF traversing =
    \case
        -- Non-trivial cases
        ExistsF any0 -> ExistsF <$> traverseVariablesExists any0
        ForallF all0 -> ForallF <$> traverseVariablesForall all0
        MuF any0 -> MuF <$> traverseVariablesMu any0
        NuF any0 -> NuF <$> traverseVariablesNu any0
        VariableF variable -> VariableF <$> traversing variable
        SetVariableF (SetVariable variable) ->
            SetVariableF . SetVariable <$> traversing variable
        -- Trivial cases
        AndF andP -> pure (AndF andP)
        ApplySymbolF applySymbolF -> pure (ApplySymbolF applySymbolF)
        ApplyAliasF applyAliasF -> pure (ApplyAliasF applyAliasF)
        BottomF botP -> pure (BottomF botP)
        BuiltinF builtinP -> pure (BuiltinF builtinP)
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
        CharLiteralF charP -> pure (CharLiteralF charP)
        TopF topP -> pure (TopF topP)
        InhabitantF s -> pure (InhabitantF s)
        EvaluatedF childP -> pure (EvaluatedF childP)
  where
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort <$> traversing existsVariable <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort <$> traversing forallVariable <*> pure forallChild
    traverseVariablesMu Mu { muVariable = SetVariable v, muChild } =
        Mu <$> (SetVariable <$> traversing v) <*> pure muChild
    traverseVariablesNu Nu { nuVariable = SetVariable v, nuChild } =
        Nu <$> (SetVariable <$> traversing v) <*> pure nuChild
