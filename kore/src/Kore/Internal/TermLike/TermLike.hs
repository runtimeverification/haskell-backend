{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.TermLike.TermLike
    ( Builtin
    , Evaluated (..)
    , TermLike (..)
    , TermLikeF (..)
    , externalizeFreshVariables
    , extractAttributes
    , freeVariables
    , mapVariables
    , traverseVariables
    , mkVar
    , traverseVariablesF
    , updateCallStack
    , depth
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Cofree
import qualified Control.Comonad.Trans.Env as Env
import Control.DeepSeq
    ( NFData (..)
    )
import qualified Control.Lens as Lens
import qualified Control.Lens.Combinators as Lens.Combinators
import Control.Monad.Reader
    ( Reader
    )
import qualified Control.Monad.Reader as Reader
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Foldable as Foldable
import Data.Functor.Adjunction
    ( Adjunction (..)
    )
import Data.Functor.Compose
    ( Compose (..)
    )
import Data.Functor.Const
    ( Const (..)
    )
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity
    ( Identity (..)
    )
import qualified Data.Generics.Product as Lens.Product
import Data.List
    ( foldl'
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC

import Generically
import qualified Kore.Attribute.Pattern as Attribute
import Kore.Attribute.Pattern.ConstructorLike
    ( HasConstructorLike (extractConstructorLike)
    )
import qualified Kore.Attribute.Pattern.ConstructorLike as Pattern
import Kore.Attribute.Pattern.Created
import qualified Kore.Attribute.Pattern.Defined as Pattern
import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Pattern.Function as Pattern
import qualified Kore.Attribute.Pattern.Functional as Pattern
import qualified Kore.Attribute.Pattern.Simplified as Pattern
import qualified Kore.Attribute.Pattern.Simplified as Simplified
    ( unparseTag
    )
import Kore.Attribute.Synthetic
import Kore.Builtin.Endianness.Endianness
    ( Endianness
    )
import Kore.Builtin.Signedness.Signedness
    ( Signedness
    )
import Kore.Debug
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Alias
import Kore.Internal.Inj
import Kore.Internal.InternalBytes
import Kore.Internal.Symbol hiding
    ( isConstructorLike
    )
import Kore.Internal.TermLike.Renaming
import Kore.Internal.Variable
import Kore.Sort
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.DomainValue
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
import Kore.Syntax.StringLiteral
import Kore.Syntax.Top
import Kore.Syntax.Variable as Variable
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Unparser as Unparser
import Kore.Variables.Binding
import Kore.Variables.Fresh
    ( FreshPartialOrd
    )
import qualified Kore.Variables.Fresh as Fresh
import qualified Pretty
import qualified SQL

{- | @Evaluated@ wraps patterns which are fully evaluated.

Fully-evaluated patterns will not be simplified further because no progress
could be made.

 -}
newtype Evaluated child = Evaluated { getEvaluated :: child }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (Evaluated child)

instance SOP.HasDatatypeInfo (Evaluated child)

instance Debug child => Debug (Evaluated child)

instance (Debug child, Diff child) => Diff (Evaluated child)

instance Hashable child => Hashable (Evaluated child)

instance NFData child => NFData (Evaluated child)

instance Unparse child => Unparse (Evaluated child) where
    unparse evaluated =
        Pretty.vsep ["/* evaluated: */", Unparser.unparseGeneric evaluated]
    unparse2 evaluated =
        Pretty.vsep ["/* evaluated: */", Unparser.unparse2Generic evaluated]

instance Synthetic syn Evaluated where
    synthetic = getEvaluated
    {-# INLINE synthetic #-}

instance {-# OVERLAPS #-} Synthetic Pattern.Simplified Evaluated where
    synthetic = const Pattern.fullySimplified
    {-# INLINE synthetic #-}

{- | 'TermLikeF' is the 'Base' functor of internal term-like patterns.

-}
data TermLikeF variable child
    = AndF           !(And Sort child)
    | ApplySymbolF   !(Application Symbol child)
    | ApplyAliasF    !(Application (Alias (TermLike Variable)) child)
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
    | BuiltinF       !(Builtin child)
    | EvaluatedF     !(Evaluated child)
    | StringLiteralF !(Const StringLiteral child)
    | InternalBytesF !(Const InternalBytes child)
    | VariableF      !(Const (UnifiedVariable variable) child)
    | EndiannessF    !(Const Endianness child)
    | SignednessF    !(Const Signedness child)
    | InjF           !(Inj child)
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic, GHC.Generic1)
    deriving
        ( Synthetic (FreeVariables variable)
        , Synthetic Sort
        , Synthetic Pattern.Functional
        , Synthetic Pattern.Function
        , Synthetic Pattern.Defined
        , Synthetic Pattern.Simplified
        , Synthetic Pattern.ConstructorLike
        ) via (Generically1 (TermLikeF variable))

instance SOP.Generic (TermLikeF variable child)

instance SOP.HasDatatypeInfo (TermLikeF variable child)

instance (Debug child, Debug variable) => Debug (TermLikeF variable child)

instance
    ( Debug child, Debug variable, Diff child, Diff variable )
    => Diff (TermLikeF variable child)

instance
    (Hashable child, Hashable variable)
    => Hashable (TermLikeF variable child)

instance (NFData child, NFData variable) => NFData (TermLikeF variable child)

instance
    ( SortedVariable variable, Unparse variable, Unparse child )
    => Unparse (TermLikeF variable child)
  where
    unparse = Unparser.unparseGeneric
    unparse2 = Unparser.unparse2Generic

newtype TermLike variable =
    TermLike
        { getTermLike
            :: Cofree (TermLikeF variable) (Attribute.Pattern variable)
        }
    deriving (GHC.Generic, Show)

instance SOP.Generic (TermLike variable)

instance SOP.HasDatatypeInfo (TermLike variable)

instance Debug variable => Debug (TermLike variable)

instance (Debug variable, Diff variable) => Diff (TermLike variable) where
    diffPrec
        termLike1@(Recursive.project -> attrs1 :< termLikeF1)
        termLike2@(Recursive.project -> _      :< termLikeF2)
      =
        -- If the patterns differ, do not display the difference in the
        -- attributes, which would overload the user with redundant information.
        diffPrecGeneric
            (Recursive.embed (attrs1 :< termLikeF1))
            (Recursive.embed (attrs1 :< termLikeF2))
        <|> diffPrecGeneric termLike1 termLike2

instance
    (Eq variable, Eq (TermLikeF variable (TermLike variable)))
    => Eq (TermLike variable)
  where
    (==)
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2)
      = pat1 == pat2

instance
    (Ord variable, Ord (TermLikeF variable (TermLike variable)))
    => Ord (TermLike variable)
  where
    compare
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2)
      = compare pat1 pat2

instance Hashable variable => Hashable (TermLike variable) where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance NFData variable => NFData (TermLike variable) where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat

instance InternalVariable variable => Unparse (TermLike variable) where
    unparse term =
        case Recursive.project freshVarTerm of
            (attrs :< termLikeF)
              | hasKnownCreator created ->
                Pretty.sep
                    [ Pretty.pretty created
                    , attributeRepresentation
                    , unparse termLikeF
                    ]
              | otherwise ->
                Pretty.sep [attributeRepresentation, unparse termLikeF]
              where
                Attribute.Pattern { created } = attrs

                attributeRepresentation = case attrs of
                    (Attribute.Pattern _ _ _ _ _ _ _ _) ->
                        Pretty.surround
                            (Pretty.hsep $ map Pretty.pretty representation)
                            "/* "
                            " */"
                  where
                    representation =
                        addFunctionalRepresentation
                        $ addFunctionRepresentation
                        $ addDefinedRepresentation
                        $ addSimplifiedRepresentation
                        $ addConstructorLikeRepresentation []
                addFunctionalRepresentation
                  | Pattern.isFunctional $ Attribute.functional attrs = ("Fl" :)
                  | otherwise = id
                addFunctionRepresentation
                  | Pattern.isFunction $ Attribute.function attrs = ("Fn" :)
                  | otherwise = id
                addDefinedRepresentation
                  | Pattern.isDefined $ Attribute.defined attrs = ("D" :)
                  | otherwise = id
                addSimplifiedRepresentation =
                    case simplifiedTag of
                        Just result -> (result :)
                        Nothing -> id
                  where
                    simplifiedTag =
                        Simplified.unparseTag
                            (Attribute.simplifiedAttribute attrs)
                addConstructorLikeRepresentation =
                    case constructorLike of
                        Just Pattern.ConstructorLikeHead -> ("Cl" :)
                        Just Pattern.SortInjectionHead -> ("Cli" :)
                        Nothing -> id
                  where
                    constructorLike =
                        Pattern.getConstructorLike
                            (Attribute.constructorLikeAttribute attrs)
      where
        freshVarTerm =
            externalizeFreshVariables
            $ mapVariables (fmap toVariable) (fmap toVariable) term

    unparse2 term =
        case Recursive.project freshVarTerm of
          (_ :< pat) -> unparse2 pat
      where
        freshVarTerm =
            externalizeFreshVariables
            $ mapVariables (fmap toVariable) (fmap toVariable) term

type instance Base (TermLike variable) =
    CofreeF (TermLikeF variable) (Attribute.Pattern variable)

-- This instance implements all class functions for the TermLike newtype
-- because the their implementations for the inner type may be specialized.
instance Recursive (TermLike variable) where
    project = \(TermLike embedded) ->
        case Recursive.project embedded of
            Compose (Identity projected) -> TermLike <$> projected
    {-# INLINE project #-}

    -- This specialization is particularly important: The default implementation
    -- of 'cata' in terms of 'project' would involve an extra call to 'fmap' at
    -- every level of the tree due to the implementation of 'project' above.
    cata alg = \(TermLike fixed) ->
        Recursive.cata
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE cata #-}

    para alg = \(TermLike fixed) ->
        Recursive.para
            (\(Compose (Identity base)) ->
                 alg (Bifunctor.first TermLike <$> base)
            )
            fixed
    {-# INLINE para #-}

    gpara dist alg = \(TermLike fixed) ->
        Recursive.gpara
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> alg (Env.local TermLike <$> base))
            fixed
    {-# INLINE gpara #-}

    prepro pre alg = \(TermLike fixed) ->
        Recursive.prepro
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE prepro #-}

    gprepro dist pre alg = \(TermLike fixed) ->
        Recursive.gprepro
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE gprepro #-}

-- This instance implements all class functions for the TermLike newtype
-- because the their implementations for the inner type may be specialized.
instance Corecursive (TermLike variable) where
    embed = \projected ->
        (TermLike . Recursive.embed . Compose . Identity)
            (getTermLike <$> projected)
    {-# INLINE embed #-}

    ana coalg = TermLike . ana0
      where
        ana0 =
            Recursive.ana (Compose . Identity . coalg)
    {-# INLINE ana #-}

    apo coalg = TermLike . apo0
      where
        apo0 =
            Recursive.apo
                (\a ->
                     (Compose . Identity)
                        (Bifunctor.first getTermLike <$> coalg a)
                )
    {-# INLINE apo #-}

    postpro post coalg = TermLike . postpro0
      where
        postpro0 =
            Recursive.postpro
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE postpro #-}

    gpostpro dist post coalg = TermLike . gpostpro0
      where
        gpostpro0 =
            Recursive.gpostpro
                (Compose . Identity . dist . (<$>) (runIdentity . getCompose))
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE gpostpro #-}

instance TopBottom (TermLike variable) where
    isTop (Recursive.project -> _ :< TopF Top {}) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomF Bottom {}) = True
    isBottom _ = False

instance InternalVariable variable => Binding (TermLike variable) where
    type VariableType (TermLike variable) = variable

    traverseElementVariable traversal termLike =
        case termLikeF of
            VariableF (Const (ElemVar elementVariable)) ->
                mkVar . ElemVar <$> traversal elementVariable
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

    traverseSetVariable traversal termLike =
        case termLikeF of
            VariableF (Const (SetVar setVariable)) ->
                mkVar . SetVar <$> traversal setVariable
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

    traverseSetBinder traversal termLike =
        case termLikeF of
            MuF mu -> synthesize . MuF <$> muBinder traversal mu
            NuF nu -> synthesize . NuF <$> nuBinder traversal nu
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

    traverseElementBinder traversal termLike =
        case termLikeF of
            ExistsF exists ->
                synthesize . ExistsF <$> existsBinder traversal exists
            ForallF forall ->
                synthesize . ForallF <$> forallBinder traversal forall
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

instance HasConstructorLike (TermLike variable) where
    extractConstructorLike (Recursive.project -> attrs :< _) =
        extractConstructorLike attrs

instance Unparse (TermLike variable) => SQL.Column (TermLike variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

instance
    (FreshPartialOrd variable, SortedVariable variable)
    => From (TermLike Concrete) (TermLike variable)
  where
    from =
        mapVariables
            (from @(ElementVariable Concrete))
            (from @(SetVariable     Concrete))
    {-# INLINE from #-}

-- | The type of internal domain values.
type Builtin = Domain.Builtin (TermLike Concrete)

{- | Use the provided mapping to replace all variables in a 'TermLikeF' head.

__Warning__: @mapVariablesF@ will capture variables if the provided mapping is
not injective!

-}
mapVariablesF
    :: (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> TermLikeF variable1 child
    -> TermLikeF variable2 child
mapVariablesF mapElemVar mapSetVar =
    runIdentity . traverseVariablesF trElemVar trSetVar
  where
    trElemVar = Identity . mapElemVar
    trSetVar = Identity . mapSetVar

{- | Use the provided traversal to replace all variables in a 'TermLikeF' head.

__Warning__: @traverseVariablesF@ will capture variables if the provided
traversal is not injective!

-}
traverseVariablesF
    :: Applicative f
    => (ElementVariable variable1 -> f (ElementVariable variable2))
    -> (SetVariable variable1 -> f (SetVariable variable2))
    ->    TermLikeF variable1 child
    -> f (TermLikeF variable2 child)
traverseVariablesF trElemVar trSetVar =
    \case
        -- Non-trivial cases
        ExistsF any0 -> ExistsF <$> traverseVariablesExists any0
        ForallF all0 -> ForallF <$> traverseVariablesForall all0
        MuF any0 -> MuF <$> traverseVariablesMu any0
        NuF any0 -> NuF <$> traverseVariablesNu any0
        VariableF variable -> VariableF <$> traverseConstVariable variable
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
        InternalBytesF bytesP -> pure (InternalBytesF bytesP)
        TopF topP -> pure (TopF topP)
        InhabitantF s -> pure (InhabitantF s)
        EvaluatedF childP -> pure (EvaluatedF childP)
        EndiannessF endianness -> pure (EndiannessF endianness)
        SignednessF signedness -> pure (SignednessF signedness)
        InjF inj -> pure (InjF inj)
  where
    traverseConstVariable (Const variable) =
        Const <$> traverseUnifiedVariable trElemVar trSetVar variable
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

extractAttributes :: TermLike variable -> Attribute.Pattern variable
extractAttributes = extract . getTermLike

instance HasFreeVariables (TermLike variable) variable where
    freeVariables = Attribute.freeVariables . extractAttributes

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

See also: 'traverseVariables'

 -}
mapVariables
    :: forall variable1 variable2
    .  (Ord variable1, FreshPartialOrd variable2, SortedVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> TermLike variable1
    -> TermLike variable2
mapVariables mapElemVar mapSetVar termLike =
    Recursive.unfold worker (Env.env freeVariables0 termLike)
  where
    trElemVar = Identity . mapElemVar
    trSetVar = Identity . mapSetVar

    Identity freeVariables0 =
        renameFreeVariables
            trElemVar
            trSetVar
            (freeVariables termLike)

    mapExists avoiding =
        sequenceAdjunct $ existsBinder $ renameElementBinder trElemVar avoiding
    mapForall avoiding =
        sequenceAdjunct $ forallBinder $ renameElementBinder trElemVar avoiding
    mapMu avoiding =
        sequenceAdjunct $ muBinder $ renameSetBinder trSetVar avoiding
    mapNu avoiding =
        sequenceAdjunct $ nuBinder $ renameSetBinder trSetVar avoiding

    askUnifiedVariable' = rightAdjunct askUnifiedVariable
    askElementVariable' = rightAdjunct askElementVariable
    askSetVariable' = rightAdjunct askSetVariable

    renameAttrs renaming =
        Attribute.mapVariables
            (askElementVariable' . Env.env renaming)
            (askSetVariable' . Env.env renaming)

    worker
        ::  Renaming variable1 variable2 (TermLike variable1)
        ->  Base
                (TermLike variable2)
                (Renaming variable1 variable2 (TermLike variable1))
    worker env =
        let attrs :< termLikeF = Recursive.project (extract env)
            renaming = Env.ask env
            attrs' = renameAttrs renaming attrs
            avoiding = getFreeVariables $ freeVariables attrs'
            termLikeF' =
                case termLikeF of
                    VariableF (Const unifiedVariable1) ->
                        (VariableF . Const)
                            (askUnifiedVariable' (env $> unifiedVariable1))
                    ExistsF exists ->
                        ExistsF (mapExists avoiding (env $> exists))
                    ForallF forall ->
                        ForallF (mapForall avoiding (env $> forall))
                    MuF mu -> MuF (mapMu avoiding (env $> mu))
                    NuF nu -> NuF (mapNu avoiding (env $> nu))
                    _ ->
                        -- mapVariablesF will not actually call the mapping
                        -- function because all the cases with variables are
                        -- handled above.
                        mapVariablesF mapElemVar mapSetVar
                        $ Env.env renaming <$> termLikeF
        in attrs' :< termLikeF'

{- | Use the provided traversal to replace all variables in a 'TermLike'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'

 -}
traverseVariables
    :: forall variable1 variable2 m
    .  (Ord variable1, FreshPartialOrd variable2, SortedVariable variable2)
    => Monad m
    => (ElementVariable variable1 -> m (ElementVariable variable2))
    -> (SetVariable variable1 -> m (SetVariable variable2))
    -> TermLike variable1
    -> m (TermLike variable2)
traverseVariables trElemVar trSetVar termLike =
    renameFreeVariables trElemVar trSetVar (freeVariables termLike)
    >>= Reader.runReaderT (Recursive.fold worker termLike)
  where
    traverseExists avoiding =
        existsBinder (renameElementBinder trElemVar avoiding)
    traverseForall avoiding =
        forallBinder (renameElementBinder trElemVar avoiding)
    traverseMu avoiding =
        muBinder (renameSetBinder trSetVar avoiding)
    traverseNu avoiding =
        nuBinder (renameSetBinder trSetVar avoiding)

    worker
        ::  Base
                (TermLike variable1)
                (RenamingT variable1 variable2 m (TermLike variable2))
        ->  RenamingT variable1 variable2 m (TermLike variable2)
    worker (attrs :< termLikeF) = do
        attrs' <-
            Attribute.traverseVariables
                askElementVariable
                askSetVariable
                attrs
        let avoiding = getFreeVariables $ freeVariables attrs'
        termLikeF' <- case termLikeF of
            VariableF (Const unifiedVariable) -> do
                unifiedVariable' <- askUnifiedVariable unifiedVariable
                (pure . VariableF) (Const unifiedVariable')
            ExistsF exists -> ExistsF <$> traverseExists avoiding exists
            ForallF forall -> ForallF <$> traverseForall avoiding forall
            MuF mu -> MuF <$> traverseMu avoiding mu
            NuF nu -> NuF <$> traverseNu avoiding nu
            _ ->
                sequence termLikeF >>=
                -- traverseVariablesF will not actually call the traversals
                -- because all the cases with variables are handled above.
                traverseVariablesF askElementVariable askSetVariable
        (pure . Recursive.embed) (attrs' :< termLikeF')

{- | Transform a 'sequence'-like function into its dual with an 'Adjunction'.

The @sequence@-like argument is a generalization of 'sequence': it lifts a
functor @g@ over a functor @t1@, allowing @t1@ to be transformed into @t2@ in
the process. The 'Adjunction' is used to transform the generalized 'sequence'
into a \"co-sequence\" which /lowers/ the adjoint functor @f@ through @t1@.

In practice,

* @f ~ Env e@ and @g ~ Reader e@
* the generalized sequence is 'renameElementBinder' or 'renameSetBinder'
* @t1@ and @t2@ are 'Binder' types with different variable types.

 -}
sequenceAdjunct
    :: forall t1 t2 g f any2
    .  Functor t1
    => Adjunction f g
    => (forall any1. t1 (g any1) -> g (t2 any1))  -- ^ 'sequence'-like function
    -> (f (t1 any2) -> t2 (f any2))
sequenceAdjunct gsequence =
    contract
    . fmap  -- inside @f@
        ( split  -- split the wrappers by lifting g out of t1
        . expand  -- wrap all values in t1
        )
  where
    -- "Expand" the values in t1 by constructing a g-f wrapper.
    -- The Adjunction allows us to "invent" a g-f wrapper for any type.
    expand :: t1 (  any2) -> t1 (g (f any2))
    --            ^              ^--^
    expand = fmap unit

    -- "Split" the g-f wrapper by lifting g over t1.
    split :: t1 (g (f any2)) -> g (t2 (f any2))
    --           ^--^           ^------^
    split = gsequence

    -- "Contract" the outer f-g wrapper to remove it
    -- The Adjunction allows us to "annihilate" an f-g wrapper.
    contract :: f (g (t2 (f any2))) ->   (t2 (f any2))
    --          ^--^                   ^
    contract = counit
{-# INLINE sequenceAdjunct #-}

renameElementBinder
    ::  Monad m
    =>  (Ord variable1, FreshPartialOrd variable2, SortedVariable variable2)
    =>  (ElementVariable variable1 -> m (ElementVariable variable2))
    ->  Set.Set (UnifiedVariable variable2)
    ->  Binder (ElementVariable variable1)
            (RenamingT variable1 variable2 m any)
    ->  RenamingT variable1 variable2 m
            (Binder (ElementVariable variable2) any)
renameElementBinder trElemVar avoiding binder = do
    let Binder { binderVariable, binderChild } = binder
    elementVariable2 <- lift $ trElemVar binderVariable
    let binderVariable' =
            refreshElementVariable avoiding elementVariable2
            & fromMaybe elementVariable2
    binderChild' <-
        Reader.local
            (renameElementVariable binderVariable binderVariable')
            binderChild
    let binder' = Binder
            { binderVariable = binderVariable'
            , binderChild = binderChild'
            }
    pure binder'
{-# INLINE renameElementBinder #-}

renameSetBinder
    ::  Monad m
    =>  (Ord variable1, FreshPartialOrd variable2, SortedVariable variable2)
    =>  (SetVariable variable1 -> m (SetVariable variable2))
    ->  Set.Set (UnifiedVariable variable2)
    ->  Binder (SetVariable variable1)
            (RenamingT variable1 variable2 m any)
    ->  RenamingT variable1 variable2 m
            (Binder (SetVariable variable2) any)
renameSetBinder trSetVar avoiding binder = do
    let Binder { binderVariable, binderChild } = binder
    setVariable2 <- lift $ trSetVar binderVariable
    let binderVariable' =
            refreshSetVariable avoiding setVariable2
            & fromMaybe setVariable2
    binderChild' <-
        Reader.local
            (renameSetVariable binderVariable binderVariable')
            binderChild
    let binder' = Binder
            { binderVariable = binderVariable'
            , binderChild = binderChild'
            }
    pure binder'
{-# INLINE renameSetBinder #-}

{- | Reset the 'variableCounter' of all 'Variables'.

@externalizeFreshVariables@ resets the 'variableCounter' of all variables, while
ensuring that no 'Variable' in the result is accidentally captured.

 -}
externalizeFreshVariables :: TermLike Variable -> TermLike Variable
externalizeFreshVariables termLike =
    Reader.runReader
        (Recursive.fold externalizeFreshVariablesWorker termLike)
        renamedFreeVariables
  where
    -- | 'originalFreeVariables' are present in the original pattern; they do
    -- not have a generated counter. 'generatedFreeVariables' have a generated
    -- counter, usually because they were introduced by applying some axiom.
    originalFreeVariables, generatedFreeVariables
        :: Set.Set (UnifiedVariable Variable)
    (originalFreeVariables, generatedFreeVariables) =
        Set.partition (foldMapVariable Variable.isOriginalVariable)
        $ getFreeVariables $ freeVariables termLike

    -- | The map of generated free variables, renamed to be unique from the
    -- original free variables.
    renamedFreeVariables :: UnifiedVariableMap Variable Variable
    (renamedFreeVariables, _) =
        Foldable.foldl' rename initial generatedFreeVariables
      where
        initial = (mempty, FreeVariables originalFreeVariables)
        rename (renaming, avoiding) variable =
            let
                (variable', renaming') =
                    case variable of
                        ElemVar elementVariable ->
                            ( ElemVar elementVariable'
                            , renameElementVariable
                                elementVariable
                                elementVariable'
                                renaming
                            )
                          where
                            elementVariable' =
                                safeElementVariable avoiding elementVariable
                        SetVar setVariable ->
                            ( SetVar setVariable'
                            , renameSetVariable
                                setVariable
                                setVariable'
                                renaming
                            )
                          where
                            setVariable' =
                                safeSetVariable avoiding setVariable
                avoiding' = freeVariable variable' <> avoiding
            in
                (renaming', avoiding')

    lookupElementVariable
        :: ElementVariable Variable
        -> Reader (UnifiedVariableMap Variable Variable) (ElementVariable Variable)
    lookupElementVariable elementVariable =
        fromMaybe elementVariable
        <$> Reader.asks (lookupRenamedElementVariable elementVariable)

    lookupSetVariable
        :: SetVariable Variable
        -> Reader (UnifiedVariableMap Variable Variable) (SetVariable Variable)
    lookupSetVariable setVariable =
        fromMaybe setVariable
        <$> Reader.asks (lookupRenamedSetVariable setVariable)

    {- | Externalize a variable safely.

    The variable's counter is incremented until its externalized form is unique
    among the set of avoided variables. The externalized form is returned.

     -}
    safeVariable
        :: (Functor f, FreshPartialOrd (f Variable))
        => (f Variable -> UnifiedVariable Variable)
        -> FreeVariables Variable
        -> f Variable
        -> f Variable
    safeVariable mk avoiding variable =
        head
        $ dropWhile wouldCapture
        $ externalize
        <$> iterate Fresh.nextVariable variable
      where
        wouldCapture var = isFreeVariable (mk var) avoiding
        externalize = fmap Variable.externalizeFreshVariable

    safeElementVariable
        :: FreeVariables Variable
        -> ElementVariable Variable
        -> ElementVariable Variable
    safeElementVariable = safeVariable ElemVar

    safeSetVariable
        :: FreeVariables Variable
        -> SetVariable Variable
        -> SetVariable Variable
    safeSetVariable = safeVariable SetVar

    underElementBinder freeVariables' variable child = do
        let variable' = safeElementVariable freeVariables' variable
        child' <- Reader.local (renameElementVariable variable variable') child
        return (variable', child')

    underSetBinder freeVariables' variable child = do
        let variable' = safeSetVariable freeVariables' variable
        child' <- Reader.local (renameSetVariable variable variable') child
        return (variable', child')

    externalizeFreshVariablesWorker
        ::  Base
                (TermLike Variable)
                (Reader
                    (UnifiedVariableMap Variable Variable)
                    (TermLike Variable)
                )
        ->  Reader
                (UnifiedVariableMap Variable Variable)
                (TermLike Variable)
    externalizeFreshVariablesWorker (attrs :< patt) = do
        attrs' <-
            Attribute.traverseVariables
                lookupElementVariable
                lookupSetVariable
                attrs
        let freeVariables' = Attribute.freeVariables attrs'
        patt' <-
            case patt of
                ExistsF exists -> do
                    let Exists { existsVariable, existsChild } = exists
                    (existsVariable', existsChild') <-
                        underElementBinder
                            freeVariables'
                            existsVariable
                            existsChild
                    let exists' =
                            exists
                                { existsVariable = existsVariable'
                                , existsChild = existsChild'
                                }
                    return (ExistsF exists')
                ForallF forall -> do
                    let Forall { forallVariable, forallChild } = forall
                    (forallVariable', forallChild') <-
                        underElementBinder
                            freeVariables'
                            forallVariable
                            forallChild
                    let forall' =
                            forall
                                { forallVariable = forallVariable'
                                , forallChild = forallChild'
                                }
                    return (ForallF forall')
                MuF mu -> do
                    let Mu { muVariable, muChild } = mu
                    (muVariable', muChild') <-
                        underSetBinder
                            freeVariables'
                            muVariable
                            muChild
                    let mu' =
                            mu
                                { muVariable = muVariable'
                                , muChild = muChild'
                                }
                    return (MuF mu')
                NuF nu -> do
                    let Nu { nuVariable, nuChild } = nu
                    (nuVariable', nuChild') <-
                        underSetBinder
                            freeVariables'
                            nuVariable
                            nuChild
                    let nu' =
                            nu
                                { nuVariable = nuVariable'
                                , nuChild = nuChild'
                                }
                    return (NuF nu')
                _ ->
                    traverseVariablesF
                        lookupElementVariable
                        lookupSetVariable
                        patt
                    >>= sequence
        (return . Recursive.embed) (attrs' :< patt')

updateCallStack
    :: forall variable
    .  HasCallStack
    => TermLike variable
    -> TermLike variable
updateCallStack = Lens.set created callstack
  where
    created = Lens.Combinators.coerced . _extract . Lens.Product.field @"created"
    callstack =
        Created . Just . GHC.popCallStack . GHC.popCallStack $ GHC.callStack

    _extract
        :: Functor f
        => (a -> f a)
        -> Cofree g a
        -> f (Cofree g a)
    _extract f (CofreeT (Identity (a :< as)))
        = CofreeT . Identity . (:< as) <$> f a

{- | Construct a variable pattern.
 -}
mkVar
    :: HasCallStack
    => InternalVariable variable
    => UnifiedVariable variable
    -> TermLike variable
mkVar = updateCallStack . synthesize . VariableF . Const

depth :: TermLike variable -> Int
depth = Recursive.fold levelDepth
  where
    levelDepth (_ :< termF) = 1 + foldl' max 0 termF
