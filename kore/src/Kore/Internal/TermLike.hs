{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.TermLike
    ( TermLikeF (..)
    , TermLike (..)
    , Evaluated (..)
    , Builtin
    , extractAttributes
    , isSimplified
    , markSimplified
    , isFunctionPattern
    , isFunctionalPattern
    , isDefinedPattern
    , freeVariables
    , refreshVariables
    , termLikeSort
    , hasFreeVariable
    , withoutFreeVariable
    , mapVariables
    , traverseVariables
    , asConcrete
    , isConcrete
    , fromConcrete
    , substitute
    , externalizeFreshVariables
    -- * Utility functions for dealing with sorts
    , forceSort
    -- * Pure Kore pattern constructors
    , mkAnd
    , mkApplyAlias
    , mkApplySymbol
    , mkBottom
    , mkBuiltin
    , mkBuiltinList
    , mkBuiltinMap
    , mkBuiltinSet
    , mkCeil
    , mkDomainValue
    , mkEquals
    , mkExists
    , mkExistsN
    , mkFloor
    , mkForall
    , mkForallN
    , mkIff
    , mkImplies
    , mkIn
    , mkMu
    , mkNext
    , mkNot
    , mkNu
    , mkOr
    , mkRewrites
    , mkTop
    , mkVar
    , mkSetVar
    , mkElemVar
    , mkStringLiteral
    , mkSort
    , mkSortVariable
    , mkInhabitant
    , mkEvaluated
    , elemVarS
    , setVarS
    -- * Predicate constructors
    , mkBottom_
    , mkCeil_
    , mkEquals_
    , mkFloor_
    , mkIn_
    , mkTop_
    -- * Sentence constructors
    , mkAlias
    , mkAlias_
    , mkAxiom
    , mkAxiom_
    , mkSymbol
    , mkSymbol_
    -- * Application constructors
    , applyAlias
    , applyAlias_
    , applySymbol
    , applySymbol_
    -- * Pattern synonyms
    , pattern And_
    , pattern ApplyAlias_
    , pattern App_
    , pattern Bottom_
    , pattern Builtin_
    , pattern BuiltinBool_
    , pattern BuiltinInt_
    , pattern BuiltinList_
    , pattern BuiltinMap_
    , pattern BuiltinSet_
    , pattern BuiltinString_
    , pattern Ceil_
    , pattern DV_
    , pattern Equals_
    , pattern Exists_
    , pattern Floor_
    , pattern Forall_
    , pattern Iff_
    , pattern Implies_
    , pattern In_
    , pattern Mu_
    , pattern Next_
    , pattern Not_
    , pattern Nu_
    , pattern Or_
    , pattern Rewrites_
    , pattern Top_
    , pattern Var_
    , pattern ElemVar_
    , pattern SetVar_
    , pattern StringLiteral_
    , pattern Evaluated_
    -- * Re-exports
    , module Kore.Internal.Variable
    , Substitute.SubstitutionVariable
    , Symbol (..)
    , Alias (..)
    , SortedVariable (..)
    , module Kore.Syntax.Id
    , CofreeF (..), Comonad (..)
    , Sort (..), SortActual (..), SortVariable (..)
    , stringMetaSort
    , module Kore.Syntax.And
    , module Kore.Syntax.Application
    , module Kore.Syntax.Bottom
    , module Kore.Syntax.Ceil
    , module Kore.Syntax.DomainValue
    , module Kore.Syntax.Equals
    , module Kore.Syntax.Exists
    , module Kore.Syntax.Floor
    , module Kore.Syntax.Forall
    , module Kore.Syntax.Iff
    , module Kore.Syntax.Implies
    , module Kore.Syntax.In
    , module Kore.Syntax.Inhabitant
    , module Kore.Syntax.Mu
    , module Kore.Syntax.Next
    , module Kore.Syntax.Not
    , module Kore.Syntax.Nu
    , module Kore.Syntax.Or
    , module Kore.Syntax.Rewrites
    , module Kore.Syntax.StringLiteral
    , module Kore.Syntax.Top
    , module Variable
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
import Data.Align
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.Function
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
import Data.Maybe
import Data.Monoid
    ( Endo (..)
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.These
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC

import Generically
import qualified Kore.Attribute.Pattern as Attribute
import Kore.Attribute.Pattern.Created
import qualified Kore.Attribute.Pattern.Defined as Pattern
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Pattern.Function as Pattern
import qualified Kore.Attribute.Pattern.Functional as Pattern
import qualified Kore.Attribute.Pattern.Simplified as Pattern
import Kore.Attribute.Synthetic
import Kore.Debug
import qualified Kore.Domain.Builtin as Domain
import Kore.Error
import Kore.Internal.Alias
import Kore.Internal.Symbol
import Kore.Internal.Variable
import Kore.Sort
import qualified Kore.Substitute as Substitute
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.Definition hiding
    ( Alias
    , Symbol
    )
import qualified Kore.Syntax.Definition as Syntax
import Kore.Syntax.DomainValue
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Id
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
    , refreshVariables
    )
import Kore.Variables.UnifiedVariable

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
    synthetic = const (Pattern.Simplified True)
    {-# INLINE synthetic #-}

-- | The type of internal domain values.
type Builtin = Domain.Builtin (TermLike Concrete)

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
    | VariableF      !(Const (UnifiedVariable variable) child)
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic, GHC.Generic1)
    deriving
        ( Synthetic (FreeVariables variable), Synthetic Sort
        , Synthetic Pattern.Functional, Synthetic Pattern.Function
        , Synthetic Pattern.Defined
        , Synthetic Pattern.Simplified
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
        TopF topP -> pure (TopF topP)
        InhabitantF s -> pure (InhabitantF s)
        EvaluatedF childP -> pure (EvaluatedF childP)
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

extractAttributes :: TermLike variable -> Attribute.Pattern variable
extractAttributes = extract . getTermLike

instance
    (Ord variable, SortedVariable variable, Show variable)
    => Binding (TermLike variable)
  where
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

freeVariables :: TermLike variable -> FreeVariables variable
freeVariables = Attribute.freeVariables . extractAttributes

hasFreeVariable
    :: Ord variable
    => UnifiedVariable variable
    -> TermLike variable
    -> Bool
hasFreeVariable variable = isFreeVariable variable . freeVariables

refreshVariables
    :: Substitute.SubstitutionVariable variable
    => FreeVariables variable
    -> TermLike variable
    -> TermLike variable
refreshVariables
    (FreeVariables.getFreeVariables -> avoid)
    term
  =
    substitute subst term
  where
    rename = Fresh.refreshVariables avoid originalFreeVariables
    originalFreeVariables = FreeVariables.getFreeVariables (freeVariables term)
    subst = mkVar <$> rename

{- | Is the 'TermLike' a function pattern?
 -}
isFunctionPattern :: TermLike variable -> Bool
isFunctionPattern =
    Pattern.isFunction . Attribute.function . extractAttributes

{- | Is the 'TermLike' functional?
 -}
isFunctionalPattern :: TermLike variable -> Bool
isFunctionalPattern =
    Pattern.isFunctional . Attribute.functional . extractAttributes

{- | Is the 'TermLike' defined, i.e. known not to be 'Bottom'?
 -}
isDefinedPattern :: TermLike variable -> Bool
isDefinedPattern =
    Pattern.isDefined . Attribute.defined . extractAttributes

{- | Throw an error if the variable occurs free in the pattern.

Otherwise, the argument is returned.

 -}
withoutFreeVariable
    :: (Ord variable, SortedVariable variable, Unparse variable)
    => UnifiedVariable variable  -- ^ variable
    -> TermLike variable
    -> a  -- ^ result, if the variable does not occur free in the pattern
    -> a
withoutFreeVariable variable termLike result
  | hasFreeVariable variable termLike =
    (error . show . Pretty.vsep)
        [ Pretty.hsep
            [ "Unexpected free variable"
            , unparse variable
            , "in pattern:"
            ]
        , Pretty.indent 4 (unparse termLike)
        ]
  | otherwise = result

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

{- | Use the provided traversal to replace all variables in a 'TermLike'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

See also: 'mapVariables'

 -}
traverseVariables
    ::  forall m variable1 variable2.
        (Monad m, Ord variable2)
    => (variable1 -> m variable2)
    -> TermLike variable1
    -> m (TermLike variable2)
traverseVariables traversing =
    Recursive.fold traverseVariablesWorker
  where
    traverseVariablesWorker (attrs :< pat) =
        Recursive.embed <$> projected
      where
        projected =
            (:<)
                <$> Attribute.traverseVariables traversing attrs
                <*> (traverseVariablesF traversing =<< sequence pat)

{- | Construct a @'TermLike' 'Concrete'@ from any 'TermLike'.

A concrete pattern contains no variables, so @asConcreteStepPattern@ is
fully polymorphic on the variable type in the pure pattern. If the argument
contains any variables, the result is @Nothing@.

@asConcrete@ is strict, i.e. it traverses its argument entirely,
because the entire tree must be traversed to inspect for variables before
deciding if the result is @Nothing@ or @Just _@.

 -}
asConcrete
    :: TermLike variable
    -> Maybe (TermLike Concrete)
asConcrete = traverseVariables (\case { _ -> Nothing })

isConcrete :: TermLike variable -> Bool
isConcrete = isJust . asConcrete

{- | Construct any 'TermLike' from a @'TermLike' 'Concrete'@.

The concrete pattern contains no variables, so the result is fully
polymorphic in the variable type.

@fromConcrete@ unfolds the resulting syntax tree lazily, so it
composes with other tree transformations without allocating intermediates.

 -}
fromConcrete
    :: Ord variable
    => TermLike Concrete
    -> TermLike variable
fromConcrete = mapVariables (\case {})

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
-- TODO (thomas.tuegel): This should normalize internal representations.
substitute
    ::  Substitute.SubstitutionVariable variable
    =>  Map (UnifiedVariable variable) (TermLike variable)
    ->  TermLike variable
    ->  TermLike variable
substitute = Substitute.substitute freeVariables

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

isSimplified :: TermLike variable -> Bool
isSimplified = Pattern.isSimplified . Attribute.simplified . extractAttributes

{- | Mark a 'TermLike' as fully simplified.

The pattern is fully simplified if we do not know how to simplify it any
further. The simplifier reserves the right to skip any pattern which is marked,
so do not mark any pattern unless you are certain it cannot be further
simplified.

 -}
markSimplified :: TermLike variable -> TermLike variable
markSimplified (Recursive.project -> attrs :< termLikeF) =
    Recursive.embed
        (attrs { Attribute.simplified = Pattern.Simplified True } :< termLikeF)

-- | Get the 'Sort' of a 'TermLike' from the 'Attribute.Pattern' annotation.
termLikeSort :: TermLike variable -> Sort
termLikeSort = Attribute.patternSort . extractAttributes

-- | Attempts to modify p to have sort s.
forceSort
    :: (SortedVariable variable, Unparse variable, GHC.HasCallStack)
    => Sort
    -> TermLike variable
    -> TermLike variable
forceSort forcedSort = Recursive.apo forceSortWorker
  where
    forceSortWorker original@(Recursive.project -> attrs :< pattern') =
        (:<)
            (attrs { Attribute.patternSort = forcedSort })
            (case attrs of
                Attribute.Pattern { patternSort = sort }
                  | sort == forcedSort    -> Left <$> pattern'
                  | sort == predicateSort -> forceSortWorkerPredicate
                  | otherwise             -> illSorted
            )
      where
        illSorted =
            (error . show . Pretty.vsep)
            [ Pretty.cat
                [ "Could not force pattern to sort "
                , Pretty.squotes (unparse forcedSort)
                , ", instead it has sort "
                , Pretty.squotes (unparse (termLikeSort original))
                , ":"
                ]
            , Pretty.indent 4 (unparse original)
            ]
        forceSortWorkerPredicate =
            case pattern' of
                -- Recurse
                EvaluatedF evaluated -> EvaluatedF (Right <$> evaluated)
                -- Predicates: Force sort and stop.
                BottomF bottom' -> BottomF bottom' { bottomSort = forcedSort }
                TopF top' -> TopF top' { topSort = forcedSort }
                CeilF ceil' -> CeilF (Left <$> ceil'')
                  where
                    ceil'' = ceil' { ceilResultSort = forcedSort }
                FloorF floor' -> FloorF (Left <$> floor'')
                  where
                    floor'' = floor' { floorResultSort = forcedSort }
                EqualsF equals' -> EqualsF (Left <$> equals'')
                  where
                    equals'' = equals' { equalsResultSort = forcedSort }
                InF in' -> InF (Left <$> in'')
                  where
                    in'' = in' { inResultSort = forcedSort }
                -- Connectives: Force sort and recurse.
                AndF and' -> AndF (Right <$> and'')
                  where
                    and'' = and' { andSort = forcedSort }
                OrF or' -> OrF (Right <$> or'')
                  where
                    or'' = or' { orSort = forcedSort }
                IffF iff' -> IffF (Right <$> iff'')
                  where
                    iff'' = iff' { iffSort = forcedSort }
                ImpliesF implies' -> ImpliesF (Right <$> implies'')
                  where
                    implies'' = implies' { impliesSort = forcedSort }
                NotF not' -> NotF (Right <$> not'')
                  where
                    not'' = not' { notSort = forcedSort }
                NextF next' -> NextF (Right <$> next'')
                  where
                    next'' = next' { nextSort = forcedSort }
                RewritesF rewrites' -> RewritesF (Right <$> rewrites'')
                  where
                    rewrites'' = rewrites' { rewritesSort = forcedSort }
                ExistsF exists' -> ExistsF (Right <$> exists'')
                  where
                    exists'' = exists' { existsSort = forcedSort }
                ForallF forall' -> ForallF (Right <$> forall'')
                  where
                    forall'' = forall' { forallSort = forcedSort }
                -- Rigid: These patterns should never have sort _PREDICATE{}.
                MuF _ -> illSorted
                NuF _ -> illSorted
                ApplySymbolF _ -> illSorted
                ApplyAliasF _ -> illSorted
                BuiltinF _ -> illSorted
                DomainValueF _ -> illSorted
                StringLiteralF _ -> illSorted
                VariableF _ -> illSorted
                InhabitantF _ -> illSorted

{- | Call the argument function with two patterns whose sorts agree.

If one pattern is flexibly sorted, the result is the rigid sort of the other
pattern. If both patterns are flexibly sorted, then the result is
'predicateSort'. If both patterns have the same rigid sort, that is the
result. It is an error if the patterns are rigidly sorted but do not have the
same sort.

 -}
makeSortsAgree
    :: (SortedVariable variable, Unparse variable, GHC.HasCallStack)
    => (TermLike variable -> TermLike variable -> Sort -> a)
    -> TermLike variable
    -> TermLike variable
    -> a
makeSortsAgree withPatterns = \pattern1 pattern2 ->
    let
        sort1 = getRigidSort pattern1
        sort2 = getRigidSort pattern2
        sort = fromMaybe predicateSort (sort1 <|> sort2)
        !pattern1' = forceSort sort pattern1
        !pattern2' = forceSort sort pattern2
    in
        withPatterns pattern1' pattern2' sort
{-# INLINE makeSortsAgree #-}

getRigidSort :: TermLike variable -> Maybe Sort
getRigidSort pattern' =
    case termLikeSort pattern' of
        sort
          | sort == predicateSort -> Nothing
          | otherwise -> Just sort

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

{- | Construct an 'And' pattern.
 -}
mkAnd
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkAnd t1 t2 = updateCallStack $ makeSortsAgree mkAndWorker t1 t2
  where
    mkAndWorker andFirst andSecond andSort =
        synthesize (AndF And { andSort, andFirst, andSecond })

{- | Force the 'TermLike's to conform to their 'Sort's.

It is an error if the lists are not the same length, or if any 'TermLike' cannot
be coerced to its corresponding 'Sort'.

See also: 'forceSort'

 -}
forceSorts
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => [Sort]
    -> [TermLike variable]
    -> [TermLike variable]
forceSorts operandSorts children =
    alignWith forceTheseSorts operandSorts children
  where
    forceTheseSorts (This _) =
        (error . show . Pretty.vsep) ("Too few arguments:" : expected)
    forceTheseSorts (That _) =
        (error . show . Pretty.vsep) ("Too many arguments:" : expected)
    forceTheseSorts (These sort termLike) = forceSort sort termLike
    expected =
        [ "Expected:"
        , Pretty.indent 4 (Unparser.arguments operandSorts)
        , "but found:"
        , Pretty.indent 4 (Unparser.arguments children)
        ]

{- | Construct an 'Application' pattern.

The result sort of the 'Alias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
mkApplyAlias
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => Alias (TermLike Variable)
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> TermLike variable
mkApplyAlias alias children =
    updateCallStack $ synthesize (ApplyAliasF application)
  where
    application =
        Application
            { applicationSymbolOrAlias = alias
            , applicationChildren = forceSorts operandSorts children
            }
    operandSorts = applicationSortsOperands (aliasSorts alias)

{- | Construct an 'Application' pattern.

The result sort of the 'SymbolOrAlias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'

 -}
mkApplySymbol
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => Symbol
    -- ^ Application symbol or alias
    -> [TermLike variable]
    -- ^ Application arguments
    -> TermLike variable
mkApplySymbol symbol children =
    updateCallStack $ synthesize (ApplySymbolF application)
  where
    application =
        Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren = forceSorts operandSorts children
            }
    operandSorts = applicationSortsOperands (symbolSorts symbol)

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApplyAlias', 'applyAlias_', 'applySymbol', 'mkAlias'

 -}
applyAlias
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SentenceAlias (TermLike Variable)
    -- ^ 'Alias' declaration
    -> [Sort]
    -- ^ 'Alias' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
applyAlias sentence params children =
    updateCallStack $ mkApplyAlias internal children'
  where
    SentenceAlias { sentenceAliasAlias = external } = sentence
    Syntax.Alias { aliasConstructor } = external
    Syntax.Alias { aliasParams } = external
    internal =
        Alias
            { aliasConstructor
            , aliasParams = params
            , aliasSorts =
                symbolOrAliasSorts params sentence
                & assertRight
            , aliasLeft =
                applicationChildren
                . sentenceAliasLeftPattern
                $ sentence
            , aliasRight = sentenceAliasRightPattern sentence
            }
    substitution = sortSubstitution aliasParams params
    childSorts = substituteSortVariables substitution <$> sentenceAliasSorts
      where
        SentenceAlias { sentenceAliasSorts } = sentence
    children' = alignWith forceChildSort childSorts children
      where
        forceChildSort =
            \case
                These sort pattern' -> forceSort sort pattern'
                This _ ->
                    (error . show . Pretty.vsep)
                        ("Too few parameters:" : expected)
                That _ ->
                    (error . show . Pretty.vsep)
                        ("Too many parameters:" : expected)
        expected =
            [ "Expected:"
            , Pretty.indent 4 (Unparser.arguments childSorts)
            , "but found:"
            , Pretty.indent 4 (Unparser.arguments children)
            ]

{- | Construct an 'Application' pattern from a 'Alias' declaration.

The 'Alias' must not be declared with sort parameters.

See also: 'mkApp', 'applyAlias'

 -}
applyAlias_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SentenceAlias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable
applyAlias_ sentence = updateCallStack . applyAlias sentence []

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The provided sort parameters must match the declaration.

See also: 'mkApp', 'applySymbol_', 'mkSymbol'

 -}
applySymbol
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SentenceSymbol pattern''
    -- ^ 'Symbol' declaration
    -> [Sort]
    -- ^ 'Symbol' sort parameters
    -> [TermLike variable]
    -- ^ 'Application' arguments
    -> TermLike variable
applySymbol sentence params children =
    updateCallStack $ mkApplySymbol internal children
  where
    SentenceSymbol { sentenceSymbolSymbol = external } = sentence
    Syntax.Symbol { symbolConstructor } = external
    internal =
        Symbol
            { symbolConstructor
            , symbolParams = params
            , symbolAttributes = Default.def
            , symbolSorts =
                symbolOrAliasSorts params sentence
                & assertRight
            }

{- | Construct an 'Application' pattern from a 'Symbol' declaration.

The 'Symbol' must not be declared with sort parameters.

See also: 'mkApplySymbol', 'applySymbol'

 -}
applySymbol_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SentenceSymbol pattern''
    -> [TermLike variable]
    -> TermLike variable
applySymbol_ sentence = updateCallStack . applySymbol sentence []

{- | Construct a 'Bottom' pattern in the given sort.

See also: 'mkBottom_'

 -}
mkBottom
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Sort
    -> TermLike variable
mkBottom bottomSort =
    updateCallStack $ synthesize (BottomF Bottom { bottomSort })

{- | Construct a 'Bottom' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkBottom' instead.

See also: 'mkBottom'

 -}
mkBottom_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
mkBottom_ = updateCallStack $ mkBottom predicateSort

{- | Construct a 'Ceil' pattern in the given sort.

See also: 'mkCeil_'

 -}
mkCeil
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
mkCeil ceilResultSort ceilChild =
    updateCallStack
        $ synthesize (CeilF Ceil { ceilOperandSort, ceilResultSort, ceilChild })
  where
    ceilOperandSort = termLikeSort ceilChild

{- | Construct a 'Ceil' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkCeil'
instead.

See also: 'mkCeil'

 -}
mkCeil_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkCeil_ = updateCallStack . mkCeil predicateSort

{- | Construct a builtin pattern.
 -}
mkBuiltin
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Domain.Builtin (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltin = updateCallStack . synthesize . BuiltinF

{- | Construct a builtin list pattern.
 -}
mkBuiltinList
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Domain.InternalList (TermLike variable)
    -> TermLike variable
mkBuiltinList = updateCallStack . synthesize . BuiltinF . Domain.BuiltinList

{- | Construct a builtin map pattern.
 -}
mkBuiltinMap
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltinMap = updateCallStack . synthesize . BuiltinF . Domain.BuiltinMap

{- | Construct a builtin set pattern.
 -}
mkBuiltinSet
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Domain.InternalSet (TermLike Concrete) (TermLike variable)
    -> TermLike variable
mkBuiltinSet = updateCallStack . synthesize . BuiltinF . Domain.BuiltinSet

{- | Construct a 'DomainValue' pattern.
 -}
mkDomainValue
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => DomainValue Sort (TermLike variable)
    -> TermLike variable
mkDomainValue = updateCallStack . synthesize . DomainValueF

{- | Construct an 'Equals' pattern in the given sort.

See also: 'mkEquals_'

 -}
mkEquals
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals equalsResultSort t1 =
    updateCallStack . makeSortsAgree mkEqualsWorker t1
  where
    mkEqualsWorker equalsFirst equalsSecond equalsOperandSort =
        synthesize (EqualsF equals)
      where
        equals =
            Equals
                { equalsOperandSort
                , equalsResultSort
                , equalsFirst
                , equalsSecond
                }

{- | Construct a 'Equals' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkEquals' instead.

See also: 'mkEquals'

 -}
mkEquals_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkEquals_ t1 t2 = updateCallStack $ mkEquals predicateSort t1 t2

{- | Construct an 'Exists' pattern.
 -}
mkExists
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => ElementVariable variable
    -> TermLike variable
    -> TermLike variable
mkExists existsVariable existsChild =
    updateCallStack
        $ synthesize (ExistsF Exists { existsSort, existsVariable, existsChild })
  where
    existsSort = termLikeSort existsChild

{- | Construct a sequence of 'Exists' patterns over several variables.
 -}
mkExistsN
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Foldable foldable
    => foldable (ElementVariable variable)
    -> TermLike variable
    -> TermLike variable
mkExistsN = (updateCallStack .) . appEndo . foldMap (Endo . mkExists)

{- | Construct a 'Floor' pattern in the given sort.

See also: 'mkFloor_'

 -}
mkFloor
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
mkFloor floorResultSort floorChild =
    updateCallStack
        $ synthesize (FloorF Floor { floorOperandSort, floorResultSort, floorChild })
  where
    floorOperandSort = termLikeSort floorChild

{- | Construct a 'Floor' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkFloor'
instead.

See also: 'mkFloor'

 -}
mkFloor_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkFloor_ = updateCallStack . mkFloor predicateSort

{- | Construct a 'Forall' pattern.
 -}
mkForall
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => ElementVariable variable
    -> TermLike variable
    -> TermLike variable
mkForall forallVariable forallChild =
    updateCallStack
        $ synthesize (ForallF Forall { forallSort, forallVariable, forallChild })
  where
    forallSort = termLikeSort forallChild

{- | Construct a sequence of 'Forall' patterns over several variables.
 -}
mkForallN
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Foldable foldable
    => foldable (ElementVariable variable)
    -> TermLike variable
    -> TermLike variable
mkForallN = (updateCallStack .) . appEndo . foldMap (Endo . mkForall)

{- | Construct an 'Iff' pattern.
 -}
mkIff
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIff t1 t2 = updateCallStack $ makeSortsAgree mkIffWorker t1 t2
  where
    mkIffWorker iffFirst iffSecond iffSort =
        synthesize (IffF Iff { iffSort, iffFirst, iffSecond })

{- | Construct an 'Implies' pattern.
 -}
mkImplies
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkImplies t1 t2 = updateCallStack $ makeSortsAgree mkImpliesWorker t1 t2
  where
    mkImpliesWorker impliesFirst impliesSecond impliesSort =
        synthesize (ImpliesF implies')
      where
        implies' = Implies { impliesSort, impliesFirst, impliesSecond }

{- | Construct a 'In' pattern in the given sort.

See also: 'mkIn_'

 -}
mkIn
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn inResultSort t1 t2 = updateCallStack $ makeSortsAgree mkInWorker t1 t2
  where
    mkInWorker inContainedChild inContainingChild inOperandSort =
        synthesize (InF in')
      where
        in' =
            In
                { inOperandSort
                , inResultSort
                , inContainedChild
                , inContainingChild
                }

{- | Construct a 'In' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use 'mkIn'
instead.

See also: 'mkIn'

 -}
mkIn_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkIn_ t1 t2 = updateCallStack $ mkIn predicateSort t1 t2

{- | Construct a 'Mu' pattern.
 -}
mkMu
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SetVariable variable
    -> TermLike variable
    -> TermLike variable
mkMu muVar = updateCallStack . makeSortsAgree mkMuWorker (mkSetVar muVar)
  where
    mkMuWorker (SetVar_ muVar') muChild _ =
        synthesize (MuF Mu { muVariable = muVar', muChild })
    mkMuWorker _ _ _ = error "Unreachable code"

{- | Construct a 'Next' pattern.
 -}
mkNext
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkNext nextChild =
    updateCallStack $ synthesize (NextF Next { nextSort, nextChild })
  where
    nextSort = termLikeSort nextChild

{- | Construct a 'Not' pattern.
 -}
mkNot
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkNot notChild =
    updateCallStack $ synthesize (NotF Not { notSort, notChild })
  where
    notSort = termLikeSort notChild

{- | Construct a 'Nu' pattern.
 -}
mkNu
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => SetVariable variable
    -> TermLike variable
    -> TermLike variable
mkNu nuVar = updateCallStack . makeSortsAgree mkNuWorker (mkSetVar nuVar)
  where
    mkNuWorker (SetVar_ nuVar') nuChild _ =
        synthesize (NuF Nu { nuVariable = nuVar', nuChild })
    mkNuWorker _ _ _ = error "Unreachable code"

{- | Construct an 'Or' pattern.
 -}
mkOr
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkOr t1 t2 = updateCallStack $ makeSortsAgree mkOrWorker t1 t2
  where
    mkOrWorker orFirst orSecond orSort =
        synthesize (OrF Or { orSort, orFirst, orSecond })

{- | Construct a 'Rewrites' pattern.
 -}
mkRewrites
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Unparse variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
mkRewrites t1 t2 = updateCallStack $ makeSortsAgree mkRewritesWorker t1 t2
  where
    mkRewritesWorker rewritesFirst rewritesSecond rewritesSort =
        synthesize (RewritesF rewrites')
      where
        rewrites' = Rewrites { rewritesSort, rewritesFirst, rewritesSecond }

{- | Construct a 'Top' pattern in the given sort.

See also: 'mkTop_'

 -}
mkTop
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Sort
    -> TermLike variable
mkTop topSort =
    updateCallStack $ synthesize (TopF Top { topSort })

{- | Construct a 'Top' pattern in 'predicateSort'.

This should not be used outside "Kore.Predicate.Predicate"; please use
'mkTop' instead.

See also: 'mkTop'

 -}
mkTop_
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
mkTop_ = updateCallStack $ mkTop predicateSort

{- | Construct a variable pattern.
 -}
mkVar
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => UnifiedVariable variable
    -> TermLike variable
mkVar = updateCallStack . synthesize . VariableF . Const

{- | Construct an element variable pattern.
 -}
mkElemVar
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => ElementVariable variable
    -> TermLike variable
mkElemVar = updateCallStack . mkVar . ElemVar

{- | Construct a set variable pattern.
 -}
mkSetVar
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => SetVariable variable
    -> TermLike variable
mkSetVar = updateCallStack . mkVar . SetVar

{- | Construct a 'StringLiteral' pattern.
 -}
mkStringLiteral
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Text
    -> TermLike variable
mkStringLiteral =
    updateCallStack . synthesize . StringLiteralF . Const . StringLiteral

mkInhabitant
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => Sort
    -> TermLike variable
mkInhabitant = updateCallStack . synthesize . InhabitantF . Inhabitant

mkEvaluated
    :: GHC.HasCallStack
    => Ord variable
    => SortedVariable variable
    => TermLike variable
    -> TermLike variable
mkEvaluated = updateCallStack . synthesize . EvaluatedF . Evaluated

mkSort :: Id -> Sort
mkSort name = SortActualSort $ SortActual name []

mkSortVariable :: Id -> Sort
mkSortVariable name = SortVariableSort $ SortVariable name

{- | Construct a variable with a given name and sort.

@
"name" `varS` sort
@
 -}
varS :: Id -> Sort -> Variable
varS variableName variableSort =
    Variable
        { variableName
        , variableSort
        , variableCounter = mempty
        }

{- | Construct an element variable with a given name and sort.

@variableName@ should *not* start with the @at@ symbol

@
"name" `elemVarS` sort
@
 -}
elemVarS :: Id -> Sort -> ElementVariable Variable
elemVarS variableName variableSort =
    ElementVariable (varS variableName variableSort)

{- | Construct a set variable with a given name and sort.

@variableName@ should start with the @at@ symbol

@
"name" `setVarS` sort
@
 -}
setVarS :: Id -> Sort -> SetVariable Variable
setVarS variableName variableSort =
    SetVariable (varS variableName variableSort)

{- | Construct an axiom declaration with the given parameters and pattern.
 -}
mkAxiom
    :: [SortVariable]
    -> TermLike variable
    -> SentenceAxiom (TermLike variable)
mkAxiom sentenceAxiomParameters sentenceAxiomPattern =
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes = Attributes []
        }

{- | Construct an axiom declaration with no parameters.

See also: 'mkAxiom'

 -}
mkAxiom_ :: TermLike variable -> SentenceAxiom (TermLike variable)
mkAxiom_ = mkAxiom []

{- | Construct a symbol declaration with the given parameters and sorts.
 -}
mkSymbol
    :: Id
    -> [SortVariable]
    -> [Sort]
    -> Sort
    -> SentenceSymbol (TermLike variable)
mkSymbol symbolConstructor symbolParams argumentSorts resultSort' =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Syntax.Symbol
                { symbolConstructor
                , symbolParams
                }
        , sentenceSymbolSorts = argumentSorts
        , sentenceSymbolResultSort = resultSort'
        , sentenceSymbolAttributes = Attributes []
        }

{- | Construct a symbol declaration with no parameters.

See also: 'mkSymbol'

 -}
mkSymbol_
    :: Id
    -> [Sort]
    -> Sort
    -> SentenceSymbol (TermLike variable)
mkSymbol_ symbolConstructor = mkSymbol symbolConstructor []

{- | Construct an alias declaration with the given parameters and sorts.
 -}
mkAlias
    :: Id
    -> [SortVariable]
    -> Sort
    -> [UnifiedVariable Variable]
    -> TermLike Variable
    -> SentenceAlias (TermLike Variable)
mkAlias aliasConstructor aliasParams resultSort' arguments right =
    SentenceAlias
        { sentenceAliasAlias =
            Syntax.Alias
                { aliasConstructor
                , aliasParams
                }
        , sentenceAliasSorts = argumentSorts
        , sentenceAliasResultSort = resultSort'
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = aliasConstructor
                        , symbolOrAliasParams =
                            SortVariableSort <$> aliasParams
                        }
                , applicationChildren = arguments
                }
        , sentenceAliasRightPattern = right
        , sentenceAliasAttributes = Attributes []
        }
  where
    argumentSorts = foldMapVariable variableSort <$> arguments

{- | Construct an alias declaration with no parameters.

See also: 'mkAlias'

 -}
mkAlias_
    :: Id
    -> Sort
    -> [UnifiedVariable Variable]
    -> TermLike Variable
    -> SentenceAlias (TermLike Variable)
mkAlias_ aliasConstructor = mkAlias aliasConstructor []

pattern And_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern App_
    :: Symbol
    -> [TermLike variable]
    -> TermLike variable

pattern ApplyAlias_
    :: Alias (TermLike Variable)
    -> [TermLike variable]
    -> TermLike variable

pattern Bottom_
    :: Sort
    -> TermLike variable

pattern Ceil_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable

pattern DV_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Builtin_
    :: Domain.Builtin (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinBool_
    :: Domain.InternalBool
    -> TermLike variable

pattern BuiltinInt_
    :: Domain.InternalInt
    -> TermLike variable

pattern BuiltinList_
    :: Domain.InternalList (TermLike variable)
    -> TermLike variable

pattern BuiltinMap_
    :: Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinSet_
    :: Domain.InternalSet (TermLike Concrete) (TermLike variable)
    -> TermLike variable

pattern BuiltinString_
    :: Domain.InternalString
    -> TermLike variable

pattern Equals_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Exists_
    :: Sort
    -> ElementVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Floor_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable

pattern Forall_
    :: Sort
    -> ElementVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Iff_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Implies_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern In_
    :: Sort
    -> Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Mu_
    :: SetVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Next_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Not_
    :: Sort
    -> TermLike variable
    -> TermLike variable

pattern Nu_
    :: SetVariable variable
    -> TermLike variable
    -> TermLike variable

pattern Or_
    :: Sort
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable

pattern Rewrites_
  :: Sort
  -> TermLike variable
  -> TermLike variable
  -> TermLike variable

pattern Top_ :: Sort -> TermLike variable

pattern Var_ :: UnifiedVariable variable -> TermLike variable

pattern ElemVar_ :: ElementVariable variable -> TermLike variable

pattern SetVar_ :: SetVariable variable -> TermLike variable

pattern StringLiteral_ :: Text -> TermLike variable

pattern Evaluated_ :: TermLike variable -> TermLike variable

pattern And_ andSort andFirst andSecond <-
    (Recursive.project -> _ :< AndF And { andSort, andFirst, andSecond })

pattern ApplyAlias_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplyAliasF Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )

pattern App_ applicationSymbolOrAlias applicationChildren <-
    (Recursive.project ->
        _ :< ApplySymbolF Application
            { applicationSymbolOrAlias
            , applicationChildren
            }
    )

pattern Bottom_ bottomSort <-
    (Recursive.project -> _ :< BottomF Bottom { bottomSort })

pattern Ceil_ ceilOperandSort ceilResultSort ceilChild <-
    (Recursive.project ->
        _ :< CeilF Ceil { ceilOperandSort, ceilResultSort, ceilChild }
    )

pattern DV_ domainValueSort domainValueChild <-
    (Recursive.project ->
        _ :< DomainValueF DomainValue { domainValueSort, domainValueChild }
    )

pattern Builtin_ builtin <- (Recursive.project -> _ :< BuiltinF builtin)

pattern BuiltinBool_ internalBool <- Builtin_ (Domain.BuiltinBool internalBool)

pattern BuiltinInt_ internalInt <- Builtin_ (Domain.BuiltinInt internalInt)

pattern BuiltinList_ internalList <- Builtin_ (Domain.BuiltinList internalList)

pattern BuiltinMap_ internalMap <- Builtin_ (Domain.BuiltinMap internalMap)

pattern BuiltinSet_ internalSet <- Builtin_ (Domain.BuiltinSet internalSet)

pattern BuiltinString_ internalString
    <- Builtin_ (Domain.BuiltinString internalString)

pattern Equals_ equalsOperandSort equalsResultSort equalsFirst equalsSecond <-
    (Recursive.project ->
        _ :< EqualsF Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
    )

pattern Exists_ existsSort existsVariable existsChild <-
    (Recursive.project ->
        _ :< ExistsF Exists { existsSort, existsVariable, existsChild }
    )

pattern Floor_ floorOperandSort floorResultSort floorChild <-
    (Recursive.project ->
        _ :< FloorF Floor
            { floorOperandSort
            , floorResultSort
            , floorChild
            }
    )

pattern Forall_ forallSort forallVariable forallChild <-
    (Recursive.project ->
        _ :< ForallF Forall { forallSort, forallVariable, forallChild }
    )

pattern Iff_ iffSort iffFirst iffSecond <-
    (Recursive.project ->
        _ :< IffF Iff { iffSort, iffFirst, iffSecond }
    )

pattern Implies_ impliesSort impliesFirst impliesSecond <-
    (Recursive.project ->
        _ :< ImpliesF Implies { impliesSort, impliesFirst, impliesSecond }
    )

pattern In_ inOperandSort inResultSort inFirst inSecond <-
    (Recursive.project ->
        _ :< InF In
            { inOperandSort
            , inResultSort
            , inContainedChild = inFirst
            , inContainingChild = inSecond
            }
    )

pattern Mu_ muVariable muChild <-
    (Recursive.project ->
        _ :< MuF Mu { muVariable, muChild }
    )

pattern Next_ nextSort nextChild <-
    (Recursive.project ->
        _ :< NextF Next { nextSort, nextChild })

pattern Not_ notSort notChild <-
    (Recursive.project ->
        _ :< NotF Not { notSort, notChild })

pattern Nu_ nuVariable nuChild <-
    (Recursive.project ->
        _ :< NuF Nu { nuVariable, nuChild }
    )

pattern Or_ orSort orFirst orSecond <-
    (Recursive.project -> _ :< OrF Or { orSort, orFirst, orSecond })

pattern Rewrites_ rewritesSort rewritesFirst rewritesSecond <-
    (Recursive.project ->
        _ :< RewritesF Rewrites
            { rewritesSort
            , rewritesFirst
            , rewritesSecond
            }
    )

pattern Top_ topSort <-
    (Recursive.project -> _ :< TopF Top { topSort })

pattern Var_ variable <-
    (Recursive.project -> _ :< VariableF (Const variable))

pattern SetVar_ setVariable <- Var_ (SetVar setVariable)

pattern ElemVar_ elemVariable <- Var_ (ElemVar elemVariable)

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralF (Const (StringLiteral str)))

pattern Evaluated_ child <-
    (Recursive.project -> _ :< EvaluatedF (Evaluated child))
