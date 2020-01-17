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
    , mkVar
    , traverseVariablesF
    , updateCallStack
    ) where

import Control.Applicative
import Control.Comonad
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
import Data.Functor.Compose
    ( Compose (..)
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
import Data.Hashable
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
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
import qualified Kore.Variables.Fresh as Fresh
    ( nextVariable
    )
import Kore.Variables.UnifiedVariable
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
    synthetic = const Pattern.Simplified
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

instance SortedVariable variable => Unparse (TermLike variable) where
    unparse term =
        case Recursive.project freshVarTerm of
            (attrs :< termLikeF)
              | hasKnownCreator created ->
                Pretty.sep [Pretty.pretty created, unparse termLikeF]
              | otherwise ->
                unparse termLikeF
              where
                Attribute.Pattern { created } = attrs
      where
        freshVarTerm =
            externalizeFreshVariables
            $ mapVariables toVariable term

    unparse2 term =
        case Recursive.project freshVarTerm of
          (_ :< pat) -> unparse2 pat
      where
        freshVarTerm =
            externalizeFreshVariables
            $ mapVariables toVariable term

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
    type VariableType (TermLike variable) = UnifiedVariable variable

    traverseVariable match termLike =
        case termLikeF of
            VariableF (Const variable) -> mkVar <$> match variable
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

    traverseBinder match termLike =
        case termLikeF of
            ExistsF exists -> synthesize . ExistsF <$> existsBinder match exists
            ForallF forall -> synthesize . ForallF <$> forallBinder match forall
            MuF mu -> synthesize . MuF <$> muBinder match mu
            NuF nu -> synthesize . NuF <$> nuBinder match nu
            _ -> pure termLike
      where
        _ :< termLikeF = Recursive.project termLike

instance HasConstructorLike (TermLike variable) where
    extractConstructorLike (Recursive.project -> attrs :< _) =
        extractConstructorLike attrs

instance Unparse (TermLike variable) => SQL.Column (TermLike variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

-- | The type of internal domain values.
type Builtin = Domain.Builtin (TermLike Concrete)

{- | Use the provided mapping to replace all variables in a 'TermLikeF' head.

__Warning__: @mapVariablesF@ will capture variables if the provided mapping is
not injective!

-}
mapVariablesF
    :: (variable1 -> variable2)
    -> TermLikeF variable1 child
    -> TermLikeF variable2 child
mapVariablesF mapping = runIdentity . traverseVariablesF (Identity . mapping)

{- | Use the provided traversal to replace all variables in a 'TermLikeF' head.

__Warning__: @traverseVariablesF@ will capture variables if the provided
traversal is not injective!

-}
traverseVariablesF
    :: Applicative f
    => (variable1 -> f variable2)
    ->    TermLikeF variable1 child
    -> f (TermLikeF variable2 child)
traverseVariablesF traversing =
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
        Const <$> traverse traversing variable
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort
        <$> traverse traversing existsVariable
        <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort
        <$> traverse traversing forallVariable
        <*> pure forallChild
    traverseVariablesMu Mu { muVariable, muChild } =
        Mu <$> traverse traversing muVariable <*> pure muChild
    traverseVariablesNu Nu { nuVariable, nuChild } =
        Nu <$> traverse traversing nuVariable <*> pure nuChild

extractAttributes :: TermLike variable -> Attribute.Pattern variable
extractAttributes = extract . getTermLike

instance HasFreeVariables (TermLike variable) variable where
    freeVariables = Attribute.freeVariables . extractAttributes

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

See also: 'traverseVariables'

 -}
mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> TermLike variable1
    -> TermLike variable2
mapVariables mapping =
    Recursive.unfold (mapVariablesWorker . Recursive.project)
  where
    mapVariablesWorker (attrs :< pat) =
        Attribute.mapVariables mapping attrs :< mapVariablesF mapping pat

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
    renamedFreeVariables :: Map Variable Variable
    (renamedFreeVariables, _) =
        Foldable.foldl' rename initial generatedFreeVariables
      where
        initial = (Map.empty, FreeVariables originalFreeVariables)
        rename (renaming, avoiding) variable =
            let
                variable' = safeVariable avoiding variable
                renaming' =
                    Map.insert
                        (asVariable variable)
                        (asVariable variable')
                        renaming
                avoiding' = freeVariable variable' <> avoiding
            in
                (renaming', avoiding')

    {- | Look up a variable renaming.

    The original (not generated) variables of the pattern are never renamed, so
    these variables are not present in the Map of renamed variables.

     -}
    lookupVariable :: Variable ->  Reader (Map Variable Variable) Variable
    lookupVariable variable =
        Reader.asks (Map.lookup variable) >>= \case
            Nothing -> return variable
            Just variable' -> return variable'

    {- | Externalize a variable safely.

    The variable's counter is incremented until its externalized form is unique
    among the set of avoided variables. The externalized form is returned.

     -}
    safeVariable
        :: FreeVariables Variable
        -> UnifiedVariable Variable
        -> UnifiedVariable Variable
    safeVariable avoiding variable =
        head  -- 'head' is safe because 'iterate' creates an infinite list
        $ dropWhile wouldCapture
        $ fmap Variable.externalizeFreshVariable
        <$> iterate (fmap Fresh.nextVariable) variable
      where
        wouldCapture var = isFreeVariable var avoiding

    underBinder freeVariables' variable child = do
        let variable' = safeVariable freeVariables' variable
        child' <- Reader.local
            (Map.insert (asVariable variable) (asVariable variable'))
            child
        return (variable', child')

    externalizeFreshVariablesWorker
        ::  Base
                (TermLike Variable)
                (Reader
                    (Map Variable Variable)
                    (TermLike Variable)
                )
        ->  Reader
                (Map Variable Variable)
                (TermLike Variable)
    externalizeFreshVariablesWorker (attrs :< patt) = do
        attrs' <- Attribute.traverseVariables lookupVariable attrs
        let freeVariables' = Attribute.freeVariables attrs'
        patt' <-
            case patt of
                ExistsF exists -> do
                    let Exists { existsVariable, existsChild } = exists
                    (existsVariable', existsChild') <-
                        underBinder
                            freeVariables'
                            (ElemVar existsVariable)
                            existsChild
                    let exists' =
                            exists
                                { existsVariable = ElementVariable
                                    (asVariable existsVariable')
                                , existsChild = existsChild'
                                }
                    return (ExistsF exists')
                ForallF forall -> do
                    let Forall { forallVariable, forallChild } = forall
                    (forallVariable', forallChild') <-
                        underBinder
                            freeVariables'
                            (ElemVar forallVariable)
                            forallChild
                    let forall' =
                            forall
                                { forallVariable = ElementVariable
                                    (asVariable forallVariable')
                                , forallChild = forallChild'
                                }
                    return (ForallF forall')
                MuF mu -> do
                    let Mu { muVariable, muChild } = mu
                    (muVariable', muChild') <-
                        underBinder
                            freeVariables'
                            (SetVar muVariable)
                            muChild
                    let mu' =
                            mu
                                { muVariable = SetVariable
                                    (asVariable muVariable')
                                , muChild = muChild'
                                }
                    return (MuF mu')
                NuF nu -> do
                    let Nu { nuVariable, nuChild } = nu
                    (nuVariable', nuChild') <-
                        underBinder
                            freeVariables'
                            (SetVar nuVariable)
                            nuChild
                    let nu' =
                            nu
                                { nuVariable = SetVariable
                                    (asVariable nuVariable')
                                , nuChild = nuChild'
                                }
                    return (NuF nu')
                _ ->
                    traverseVariablesF lookupVariable patt >>= sequence
        (return . Recursive.embed) (attrs' :< patt')
    --TODO(traiansf): consider removing this usage of asVariable
    asVariable :: UnifiedVariable variable -> variable
    asVariable = foldMapVariable id

updateCallStack
    :: forall variable
    .  GHC.HasCallStack
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
    :: GHC.HasCallStack
    => InternalVariable variable
    => UnifiedVariable variable
    -> TermLike variable
mkVar = updateCallStack . synthesize . VariableF . Const
