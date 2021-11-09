{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Validate.Pattern (
    Pattern,
    PatternF (..),
    PatternAttributes (..),
    extractAttributes,
    patternSort,
    setSimplified,
    isSimplified,
    forgetSimplified,
    setAttributeSimplified,
    mapVariables,
    Modality (..),
    applyModality,
    updateCallStack,
    samePatternSort,

    mkAxiom,
    mkAxiom_,

    -- * Pure Kore pattern constructors
    mkAnd,
    mkApplyAlias,
    mkApplySymbol,
    mkBottom,
    mkInternalBytes,
    mkInternalBytes',
    mkInternalBool,
    mkInternalInt,
    mkInternalString,
    mkInternalList,
    mkInternalMap,
    mkInternalSet,
    mkCeil,
    mkDomainValue,
    mkEquals,
    mkExists,
    mkExistsN,
    mkFloor,
    mkForall,
    mkForallN,
    mkIff,
    mkImplies,
    mkIn,
    mkMu,
    mkNext,
    mkNot,
    mkNu,
    mkOr,
    mkRewrites,
    mkTop,
    mkVar,
    mkSetVar,
    mkElemVar,
    mkStringLiteral,
    mkSort,
    mkSortVariable,
    mkInhabitant,
    mkEndianness,
    mkSignedness,
    symbolApplication,

    -- * Pattern synonyms
    pattern And_,
    pattern ApplyAlias_,
    pattern App_,
    pattern Bottom_,
    pattern InternalBytes_,
    pattern InternalBool_,
    pattern InternalInt_,
    pattern InternalList_,
    pattern InternalMap_,
    pattern InternalSet_,
    pattern InternalString_,
    pattern Ceil_,
    pattern DV_,
    pattern Equals_,
    pattern Exists_,
    pattern Floor_,
    pattern Forall_,
    pattern Iff_,
    pattern Implies_,
    pattern In_,
    pattern Mu_,
    pattern Next_,
    pattern Not_,
    pattern Nu_,
    pattern Or_,
    pattern Rewrites_,
    pattern Top_,
    pattern Var_,
    pattern ElemVar_,
    pattern SetVar_,
    pattern StringLiteral_,
    pattern Endianness_,
    pattern Signedness_,
    pattern Inj_,
) where

import Control.Comonad.Trans.Cofree (
    tailF,
 )
import qualified Kore.Syntax.Definition as Syntax
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Error (assertRight)
import Kore.Attribute.Attributes (Attributes (..))
import Kore.Syntax.Sentence (SentenceAxiom (..)
  , SentenceSymbol (..)
  , SentenceAlias (..)
                    )
import Control.Lens (
    Lens',
 )
import qualified Control.Lens as Lens
import qualified Control.Monad.Reader as Reader
import Data.Align (
    alignWith,
 )
import Data.ByteString (
    ByteString,
 )
import Data.Functor.Const (
    Const (..),
 )
import Data.Functor.Foldable (
    Base,
    Corecursive (..),
    Recursive (..),
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity (Identity, runIdentity)
import qualified Data.Generics.Product as Lens.Product
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Semigroup (Endo (..), appEndo)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.These
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC
import qualified Generics.SOP as SOP
import Kore.AST.AstWithLocation
import qualified Kore.Attribute.Pattern.ConstructorLike as Attribute
import qualified Kore.Attribute.Pattern.Created as Attribute
import qualified Kore.Attribute.Pattern.Defined as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute
import qualified Kore.Attribute.Pattern.Function as Attribute
import qualified Kore.Attribute.Pattern.Functional as Attribute
import qualified Kore.Attribute.Pattern.Simplified as Attribute
import qualified Kore.Attribute.Pattern.Simplified as Attribute.Simplified
import Kore.Attribute.Synthetic
import Kore.Builtin.Endianness.Endianness (
    Endianness,
 )
import Kore.Builtin.Signedness.Signedness (
    Signedness,
 )
import Kore.Debug
import Kore.Internal.Alias
import Kore.Internal.Inj
import Kore.Internal.InternalBool
import Kore.Internal.InternalBytes
import Kore.Internal.InternalInt
import Kore.Internal.InternalList
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.InternalString
import Kore.Internal.Key (
    Key,
 )
import Kore.Internal.Symbol
import Kore.Internal.TermLike.Renaming
import Kore.Internal.Variable
import Kore.Sort
import Kore.Substitute
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
import Kore.TopBottom
import Kore.Unparser (Unparse (..))
import qualified Kore.Unparser as Unparser
import Kore.Variables.Binding
import Kore.Variables.Fresh (refreshVariable)
import Prelude.Kore
import qualified Pretty

-- | 'PatternF' is the 'Base' functor of validated patterns.
data PatternF variable child
    = AndF !(And Sort child)
    | ApplySymbolF !(Application Symbol child)
    | -- TODO (thomas.tuegel): Expand aliases during validation?
      ApplyAliasF !(Application (Alias (Pattern VariableName)) child)
    | BottomF !(Bottom Sort child)
    | CeilF !(Ceil Sort child)
    | DomainValueF !(DomainValue Sort child)
    | EqualsF !(Equals Sort child)
    | ExistsF !(Exists Sort variable child)
    | FloorF !(Floor Sort child)
    | ForallF !(Forall Sort variable child)
    | IffF !(Iff Sort child)
    | ImpliesF !(Implies Sort child)
    | InF !(In Sort child)
    | MuF !(Mu variable child)
    | NextF !(Next Sort child)
    | NotF !(Not Sort child)
    | NuF !(Nu variable child)
    | OrF !(Or Sort child)
    | RewritesF !(Rewrites Sort child)
    | TopF !(Top Sort child)
    | InhabitantF !(Inhabitant child)
    | StringLiteralF !(Const StringLiteral child)
    | InternalBoolF !(Const InternalBool child)
    | InternalBytesF !(Const InternalBytes child)
    | InternalIntF !(Const InternalInt child)
    | InternalStringF !(Const InternalString child)
    | InternalListF !(InternalList child)
    | InternalMapF !(InternalMap Key child)
    | InternalSetF !(InternalSet Key child)
    | VariableF !(Const (SomeVariable variable) child)
    | EndiannessF !(Const Endianness child)
    | SignednessF !(Const Signedness child)
    | InjF !(Inj child)
    deriving stock (Eq, Ord, Show)
    deriving stock (Foldable, Functor, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    ( AstWithLocation child
    , AstWithLocation variable
    ) =>
    AstWithLocation (PatternF variable child)
    where
    locationFromAst =
        \case
            AndF And{andSort} -> locationFromAst andSort
            ApplySymbolF Application{applicationSymbolOrAlias} ->
                locationFromAst applicationSymbolOrAlias
            ApplyAliasF Application{applicationSymbolOrAlias} ->
                locationFromAst applicationSymbolOrAlias
            BottomF Bottom{bottomSort} -> locationFromAst bottomSort
            CeilF Ceil{ceilResultSort} -> locationFromAst ceilResultSort
            DomainValueF domain -> locationFromAst $ domainValueSort domain
            EqualsF Equals{equalsResultSort} ->
                locationFromAst equalsResultSort
            ExistsF Exists{existsSort} -> locationFromAst existsSort
            FloorF Floor{floorResultSort} ->
                locationFromAst floorResultSort
            ForallF Forall{forallSort} -> locationFromAst forallSort
            IffF Iff{iffSort} -> locationFromAst iffSort
            ImpliesF Implies{impliesSort} ->
                locationFromAst impliesSort
            InF In{inResultSort} -> locationFromAst inResultSort
            MuF Mu{muVariable} -> locationFromAst muVariable
            NextF Next{nextSort} -> locationFromAst nextSort
            NotF Not{notSort} -> locationFromAst notSort
            NuF Nu{nuVariable} -> locationFromAst nuVariable
            OrF Or{orSort} -> locationFromAst orSort
            RewritesF Rewrites{rewritesSort} ->
                locationFromAst rewritesSort
            StringLiteralF _ -> AstLocationUnknown
            TopF Top{topSort} -> locationFromAst topSort
            VariableF (Const variable) -> locationFromAst variable
            InhabitantF Inhabitant{inhSort} -> locationFromAst inhSort
            InjF Inj{injChild} -> locationFromAst injChild
            SignednessF (Const signedness) -> locationFromAst signedness
            EndiannessF (Const endianness) -> locationFromAst endianness
            InternalBoolF (Const InternalBool{internalBoolSort}) ->
                locationFromAst internalBoolSort
            InternalBytesF (Const InternalBytes{internalBytesSort}) ->
                locationFromAst internalBytesSort
            InternalIntF (Const InternalInt{internalIntSort}) ->
                locationFromAst internalIntSort
            InternalStringF (Const InternalString{internalStringSort}) ->
                locationFromAst internalStringSort
            InternalListF InternalList{internalListSort} ->
                locationFromAst internalListSort
            InternalMapF InternalAc{builtinAcSort} ->
                locationFromAst builtinAcSort
            InternalSetF InternalAc{builtinAcSort} ->
                locationFromAst builtinAcSort

instance
    Ord variable =>
    Synthetic (Attribute.FreeVariables variable) (PatternF variable)
    where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Sort (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Attribute.Functional (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Attribute.Function (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Attribute.Defined (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Attribute.Simplified (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance Synthetic Attribute.ConstructorLike (PatternF variable) where
    synthetic =
        \case
            AndF and' -> synthetic and'
            ApplySymbolF application -> synthetic application
            ApplyAliasF application -> synthetic application
            BottomF bottom -> synthetic bottom
            CeilF ceil -> synthetic ceil
            DomainValueF domainValue -> synthetic domainValue
            EqualsF equals -> synthetic equals
            ExistsF exists -> synthetic exists
            FloorF floor' -> synthetic floor'
            ForallF forall' -> synthetic forall'
            IffF iff -> synthetic iff
            ImpliesF implies -> synthetic implies
            InF in' -> synthetic in'
            MuF mu -> synthetic mu
            NextF next -> synthetic next
            NotF not' -> synthetic not'
            NuF nu -> synthetic nu
            OrF or' -> synthetic or'
            RewritesF rewrites -> synthetic rewrites
            TopF top -> synthetic top
            InhabitantF inhabitant -> synthetic inhabitant
            StringLiteralF stringLiteral -> synthetic stringLiteral
            InternalBoolF internalBool -> synthetic internalBool
            InternalBytesF internalBytes -> synthetic internalBytes
            InternalIntF internalInt -> synthetic internalInt
            InternalStringF internalString -> synthetic internalString
            InternalListF internalList -> synthetic internalList
            InternalMapF internalMap -> synthetic internalMap
            InternalSetF internalSet -> synthetic internalSet
            VariableF variable -> synthetic variable
            EndiannessF endianness -> synthetic endianness
            SignednessF signedness -> synthetic signedness
            InjF inj -> synthetic inj

instance (Unparse variable, Unparse child) => Unparse (PatternF variable child) where
    unparse = Unparser.unparseGeneric
    unparse2 = Unparser.unparse2Generic

newtype Pattern variable = Pattern
    { getPattern ::
        CofreeF
            (PatternF variable)
            (PatternAttributes variable)
            (Pattern variable)
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

type instance
    Base (Pattern variable) =
        CofreeF (PatternF variable) (PatternAttributes variable)

instance Recursive (Pattern variable) where
    project = getPattern
    {-# INLINE project #-}

instance Corecursive (Pattern variable) where
    embed = Pattern
    {-# INLINE embed #-}

instance TopBottom (Pattern variable) where
    isTop (Recursive.project -> _ :< TopF Top{}) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomF Bottom{}) = True
    isBottom _ = False

instance Attribute.HasFreeVariables (Pattern variable) variable where
    freeVariables = Attribute.freeVariables . extractAttributes

instance AstWithLocation variable => AstWithLocation (Pattern variable) where
    locationFromAst = locationFromAst . tailF . Recursive.project

instance (Debug variable, Diff variable) => Diff (Pattern variable) where
    diffPrec
        termLike1@(Recursive.project -> attrs1 :< termLikeF1)
        termLike2@(Recursive.project -> _ :< termLikeF2) =
            -- If the patterns differ, do not display the difference in the
            -- attributes, which would overload the user with redundant information.
            diffPrecGeneric
                (Recursive.embed (attrs1 :< termLikeF1))
                (Recursive.embed (attrs1 :< termLikeF2))
                <|> diffPrecGeneric termLike1 termLike2

instance
    (Eq variable, Eq (PatternF variable (Pattern variable))) =>
    Eq (Pattern variable)
    where
    (==)
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2) =
            pat1 == pat2

instance
    (Ord variable, Ord (PatternF variable (Pattern variable))) =>
    Ord (Pattern variable)
    where
    compare
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2) =
            compare pat1 pat2

instance Hashable variable => Hashable (Pattern variable) where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance NFData variable => NFData (Pattern variable) where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat

-- TODO: can this and Pattern's instance be factored out?
instance Unparse variable => Unparse (Pattern variable) where
    unparse term =
        case Recursive.project term of
            (attrs :< termLikeF)
                | Attribute.hasKnownCreator termCreated ->
                    Pretty.sep
                        [ Pretty.pretty termCreated
                        , attributeRepresentation
                        , unparse termLikeF
                        ]
                | otherwise ->
                    Pretty.sep [attributeRepresentation, unparse termLikeF]
              where
                PatternAttributes{termCreated} = attrs

                attributeRepresentation = case attrs of
                    (PatternAttributes _ _ _ _ _ _ _ _) ->
                        Pretty.surround
                            (Pretty.hsep $ map Pretty.pretty representation)
                            "/* "
                            " */"
                  where
                    representation =
                        addFunctionalRepresentation $
                            addFunctionRepresentation $
                                addDefinedRepresentation $
                                    addSimplifiedRepresentation $
                                        addConstructorLikeRepresentation []
                addFunctionalRepresentation
                    | Attribute.isFunctional $ termFunctional attrs = ("Fl" :)
                    | otherwise = id
                addFunctionRepresentation
                    | Attribute.isFunction $ termFunction attrs = ("Fn" :)
                    | otherwise = id
                addDefinedRepresentation
                    | Attribute.isDefined $ termDefined attrs = ("D" :)
                    | otherwise = id
                addSimplifiedRepresentation =
                    case simplifiedTag of
                        Just result -> (result :)
                        Nothing -> id
                  where
                    simplifiedTag =
                        Attribute.Simplified.unparseTag
                            (attributeSimplifiedAttribute attrs)
                addConstructorLikeRepresentation =
                    case constructorLike of
                        Just Attribute.ConstructorLikeHead -> ("Cl" :)
                        Just Attribute.SortInjectionHead -> ("Cli" :)
                        Nothing -> id
                  where
                    constructorLike =
                        Attribute.getConstructorLike
                            (constructorLikeAttribute attrs)

    unparse2 term =
        case Recursive.project term of
            (_ :< pat) -> unparse2 pat

-- | @PatternAttributes@ are the attributes of a pattern collected during validation.
data PatternAttributes variable = PatternAttributes
    { termSort :: !Sort
    , termFreeVariables :: !(Attribute.FreeVariables variable)
    , termFunctional :: !Attribute.Functional
    , termFunction :: !Attribute.Function
    , termDefined :: !Attribute.Defined
    , termCreated :: !Attribute.Created
    , termSimplified :: !Attribute.Simplified
    , termConstructorLike :: !Attribute.ConstructorLike
    }
    deriving stock (Eq, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

instance Attribute.HasFreeVariables (PatternAttributes variable) variable where
    freeVariables = termFreeVariables

instance (Debug variable, Diff variable) => Diff (PatternAttributes variable)

instance
    ( Functor base
    , Synthetic Sort base
    , Synthetic (Attribute.FreeVariables variable) base
    , Synthetic Attribute.Functional base
    , Synthetic Attribute.Function base
    , Synthetic Attribute.Defined base
    , Synthetic Attribute.Simplified base
    , Synthetic Attribute.ConstructorLike base
    ) =>
    Synthetic (PatternAttributes variable) base
    where
    synthetic base =
        PatternAttributes
            { termSort = synthetic (termSort <$> base)
            , termFreeVariables = synthetic (termFreeVariables <$> base)
            , termFunctional = synthetic (termFunctional <$> base)
            , termFunction = synthetic (termFunction <$> base)
            , termDefined = synthetic (termDefined <$> base)
            , termCreated = synthetic (termCreated <$> base)
            , termSimplified =
                if Attribute.isConstructorLike constructorLikeAttr
                    then Attribute.fullySimplified
                    else synthetic (termSimplified <$> base)
            , termConstructorLike = constructorLikeAttr
            }
      where
        constructorLikeAttr :: Attribute.ConstructorLike
        constructorLikeAttr = synthetic (termConstructorLike <$> base)

instance Attribute.HasConstructorLike (PatternAttributes variable) where
    extractConstructorLike
        PatternAttributes{termConstructorLike} =
            termConstructorLike

attributeSimplifiedAttribute ::
    HasCallStack =>
    PatternAttributes variable ->
    Attribute.Simplified
attributeSimplifiedAttribute patt@PatternAttributes{termSimplified} =
    assertSimplifiedConsistency patt termSimplified

constructorLikeAttribute ::
    PatternAttributes variable ->
    Attribute.ConstructorLike
constructorLikeAttribute PatternAttributes{termConstructorLike} =
    termConstructorLike

assertSimplifiedConsistency ::
    HasCallStack =>
    PatternAttributes variable ->
    a ->
    a
assertSimplifiedConsistency
    PatternAttributes{termConstructorLike, termSimplified}
        | Attribute.isConstructorLike termConstructorLike
          , not (Attribute.isSimplifiedAnyCondition termSimplified) =
            error "Inconsistent attributes, constructorLike implies fully simplified."
        | otherwise = id

pattern And_ ::
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern App_ ::
    Symbol ->
    [Pattern variable] ->
    Pattern variable

pattern ApplyAlias_ ::
    Alias (Pattern VariableName) ->
    [Pattern variable] ->
    Pattern variable

pattern Bottom_ ::
    Sort ->
    Pattern variable

pattern Ceil_ ::
    Sort ->
    Sort ->
    Pattern variable ->
    Pattern variable

pattern DV_ ::
    Sort ->
    Pattern variable ->
    Pattern variable

pattern InternalBool_ ::
    InternalBool ->
    Pattern variable

pattern InternalInt_ ::
    InternalInt ->
    Pattern variable

pattern InternalList_ ::
    InternalList (Pattern variable) ->
    Pattern variable

pattern InternalMap_ ::
    InternalMap Key (Pattern variable) ->
    Pattern variable

pattern InternalSet_ ::
    InternalSet Key (Pattern variable) ->
    Pattern variable

pattern InternalString_ :: InternalString -> Pattern variable

pattern Equals_ ::
    Sort ->
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern Exists_ ::
    Sort ->
    ElementVariable variable ->
    Pattern variable ->
    Pattern variable

pattern Floor_ ::
    Sort ->
    Sort ->
    Pattern variable ->
    Pattern variable

pattern Forall_ ::
    Sort ->
    ElementVariable variable ->
    Pattern variable ->
    Pattern variable

pattern Iff_ ::
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern Implies_ ::
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern In_ ::
    Sort ->
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern Mu_ ::
    SetVariable variable ->
    Pattern variable ->
    Pattern variable

pattern Next_ ::
    Sort ->
    Pattern variable ->
    Pattern variable

pattern Not_ ::
    Sort ->
    Pattern variable ->
    Pattern variable

pattern Nu_ ::
    SetVariable variable ->
    Pattern variable ->
    Pattern variable

pattern Or_ ::
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern Rewrites_ ::
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable

pattern Top_ :: Sort -> Pattern variable
pattern Var_ :: SomeVariable variable -> Pattern variable
pattern ElemVar_ :: ElementVariable variable -> Pattern variable
pattern SetVar_ :: SetVariable variable -> Pattern variable
pattern StringLiteral_ :: Text -> Pattern variable
pattern And_ andSort andFirst andSecond <-
    (Recursive.project -> _ :< AndF And{andSort, andFirst, andSecond})

pattern ApplyAlias_ applicationSymbolOrAlias applicationChildren <-
    ( Recursive.project ->
            _
                :< ApplyAliasF
                    Application
                        { applicationSymbolOrAlias
                        , applicationChildren
                        }
        )

pattern App_ applicationSymbolOrAlias applicationChildren <-
    ( Recursive.project ->
            _
                :< ApplySymbolF
                    Application
                        { applicationSymbolOrAlias
                        , applicationChildren
                        }
        )

pattern Bottom_ bottomSort <-
    (Recursive.project -> _ :< BottomF Bottom{bottomSort})

pattern InternalBytes_ :: Sort -> ByteString -> Pattern variable
pattern InternalBytes_ internalBytesSort internalBytesValue <-
    ( Recursive.project ->
            _
                :< InternalBytesF
                    ( Const
                            InternalBytes
                                { internalBytesSort
                                , internalBytesValue
                                }
                        )
        )

pattern Ceil_ ceilOperandSort ceilResultSort ceilChild <-
    ( Recursive.project ->
            _ :< CeilF Ceil{ceilOperandSort, ceilResultSort, ceilChild}
        )

pattern DV_ domainValueSort domainValueChild <-
    ( Recursive.project ->
            _ :< DomainValueF DomainValue{domainValueSort, domainValueChild}
        )

pattern InternalBool_ internalBool <-
    (Recursive.project -> _ :< InternalBoolF (Const internalBool))

pattern InternalInt_ internalInt <-
    (Recursive.project -> _ :< InternalIntF (Const internalInt))

pattern InternalString_ internalString <-
    (Recursive.project -> _ :< InternalStringF (Const internalString))

pattern InternalList_ internalList <-
    (Recursive.project -> _ :< InternalListF internalList)

pattern InternalMap_ internalMap <-
    (Recursive.project -> _ :< InternalMapF internalMap)

pattern InternalSet_ internalSet <-
    (Recursive.project -> _ :< InternalSetF internalSet)

pattern Equals_ equalsOperandSort equalsResultSort equalsFirst equalsSecond <-
    ( Recursive.project ->
            _
                :< EqualsF
                    Equals
                        { equalsOperandSort
                        , equalsResultSort
                        , equalsFirst
                        , equalsSecond
                        }
        )

pattern Exists_ existsSort existsVariable existsChild <-
    ( Recursive.project ->
            _ :< ExistsF Exists{existsSort, existsVariable, existsChild}
        )

pattern Floor_ floorOperandSort floorResultSort floorChild <-
    ( Recursive.project ->
            _
                :< FloorF
                    Floor
                        { floorOperandSort
                        , floorResultSort
                        , floorChild
                        }
        )

pattern Forall_ forallSort forallVariable forallChild <-
    ( Recursive.project ->
            _ :< ForallF Forall{forallSort, forallVariable, forallChild}
        )

pattern Iff_ iffSort iffFirst iffSecond <-
    ( Recursive.project ->
            _ :< IffF Iff{iffSort, iffFirst, iffSecond}
        )

pattern Implies_ impliesSort impliesFirst impliesSecond <-
    ( Recursive.project ->
            _ :< ImpliesF Implies{impliesSort, impliesFirst, impliesSecond}
        )

pattern In_ inOperandSort inResultSort inFirst inSecond <-
    ( Recursive.project ->
            _
                :< InF
                    In
                        { inOperandSort
                        , inResultSort
                        , inContainedChild = inFirst
                        , inContainingChild = inSecond
                        }
        )

pattern Mu_ muVariable muChild <-
    ( Recursive.project ->
            _ :< MuF Mu{muVariable, muChild}
        )

pattern Next_ nextSort nextChild <-
    ( Recursive.project ->
            _ :< NextF Next{nextSort, nextChild}
        )

pattern Not_ notSort notChild <-
    ( Recursive.project ->
            _ :< NotF Not{notSort, notChild}
        )

pattern Nu_ nuVariable nuChild <-
    ( Recursive.project ->
            _ :< NuF Nu{nuVariable, nuChild}
        )

pattern Or_ orSort orFirst orSecond <-
    (Recursive.project -> _ :< OrF Or{orSort, orFirst, orSecond})

pattern Rewrites_ rewritesSort rewritesFirst rewritesSecond <-
    ( Recursive.project ->
            _
                :< RewritesF
                    Rewrites
                        { rewritesSort
                        , rewritesFirst
                        , rewritesSecond
                        }
        )

pattern Top_ topSort <-
    (Recursive.project -> _ :< TopF Top{topSort})

pattern Var_ variable <-
    (Recursive.project -> _ :< VariableF (Const variable))

pattern SetVar_ setVariable <- Var_ (retract -> Just setVariable)

pattern ElemVar_ elemVariable <- Var_ (retract -> Just elemVariable)

pattern StringLiteral_ str <-
    (Recursive.project -> _ :< StringLiteralF (Const (StringLiteral str)))

pattern Endianness_ :: Endianness -> Pattern variable
pattern Endianness_ endianness <-
    (Recursive.project -> _ :< EndiannessF (Const endianness))

pattern Signedness_ :: Signedness -> Pattern variable
pattern Signedness_ signedness <-
    (Recursive.project -> _ :< SignednessF (Const signedness))

pattern Inj_ :: Inj (Pattern variable) -> Pattern variable
pattern Inj_ inj <- (Recursive.project -> _ :< InjF inj)

extractAttributes :: Pattern variable -> PatternAttributes variable
extractAttributes (Pattern (attrs :< _)) = attrs

-- | Get the 'Sort' of a 'Pattern' from the 'Attribute.Pattern' annotation.
patternSort :: Pattern variable -> Sort
patternSort = termSort . extractAttributes

-- | Construct an 'And' pattern.
mkAnd ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkAnd t1 t2 = updateCallStack $ checkSortsAgree mkAndWorker t1 t2
  where
    mkAndWorker andFirst andSecond andSort =
        synthesize (AndF And{andSort, andFirst, andSecond})

{- | Construct an 'Application' pattern.

The result sort of the 'Alias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'
-}
mkApplyAlias ::
    HasCallStack =>
    InternalVariable variable =>
    -- | Application symbol or alias
    Alias (Pattern VariableName) ->
    -- | Application arguments
    [Pattern variable] ->
    Pattern variable
mkApplyAlias alias children =
    updateCallStack $ synthesize (ApplyAliasF application)
  where
    application =
        Application
            { applicationSymbolOrAlias = alias
            , applicationChildren = samePatternSorts operandSorts children
            }
    operandSorts = applicationSortsOperands (aliasSorts alias)

{- | Construct an 'Application' pattern.

The result sort of the 'SymbolOrAlias' must be provided. The sorts of arguments
are not checked. Use 'applySymbol' or 'applyAlias' whenever possible to avoid
these shortcomings.

See also: 'applyAlias', 'applySymbol'
-}
mkApplySymbol ::
    HasCallStack =>
    InternalVariable variable =>
    -- | Application symbol or alias
    Symbol ->
    -- | Application arguments
    [Pattern variable] ->
    Pattern variable
mkApplySymbol symbol children =
    updateCallStack $
        synthesize (ApplySymbolF (symbolApplication symbol children))

symbolApplication ::
    HasCallStack =>
    InternalVariable variable =>
    -- | Application symbol or alias
    Symbol ->
    -- | Application arguments
    [Pattern variable] ->
    Application Symbol (Pattern variable)
symbolApplication symbol children =
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = samePatternSorts operandSorts children
        }
  where
    operandSorts = applicationSortsOperands (symbolSorts symbol)

-- | Construct a 'Bottom' pattern in the given sort.
mkBottom ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable
mkBottom bottomSort =
    updateCallStack $ synthesize (BottomF Bottom{bottomSort})

-- | Construct a 'Ceil' pattern in the given sort.
mkCeil ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable ->
    Pattern variable
mkCeil ceilResultSort ceilChild =
    updateCallStack $
        synthesize (CeilF Ceil{ceilOperandSort, ceilResultSort, ceilChild})
  where
    ceilOperandSort = patternSort ceilChild

-- | Construct an internal bool pattern.
mkInternalBool ::
    HasCallStack =>
    InternalVariable variable =>
    InternalBool ->
    Pattern variable
mkInternalBool = updateCallStack . synthesize . InternalBoolF . Const

-- | Construct an internal integer pattern.
mkInternalInt ::
    HasCallStack =>
    InternalVariable variable =>
    InternalInt ->
    Pattern variable
mkInternalInt = updateCallStack . synthesize . InternalIntF . Const

-- | Construct an internal string pattern.
mkInternalString ::
    HasCallStack =>
    InternalVariable variable =>
    InternalString ->
    Pattern variable
mkInternalString = updateCallStack . synthesize . InternalStringF . Const

-- | Construct a builtin list pattern.
mkInternalList ::
    HasCallStack =>
    InternalVariable variable =>
    InternalList (Pattern variable) ->
    Pattern variable
mkInternalList = updateCallStack . synthesize . InternalListF

-- | Construct a builtin map pattern.
mkInternalMap ::
    HasCallStack =>
    InternalVariable variable =>
    InternalMap Key (Pattern variable) ->
    Pattern variable
mkInternalMap = updateCallStack . synthesize . InternalMapF

-- | Construct a builtin set pattern.
mkInternalSet ::
    HasCallStack =>
    InternalVariable variable =>
    InternalSet Key (Pattern variable) ->
    Pattern variable
mkInternalSet = updateCallStack . synthesize . InternalSetF

-- | Construct a 'DomainValue' pattern.
mkDomainValue ::
    HasCallStack =>
    InternalVariable variable =>
    DomainValue Sort (Pattern variable) ->
    Pattern variable
mkDomainValue = updateCallStack . synthesize . DomainValueF

-- | Construct an 'Equals' pattern in the given sort.
mkEquals ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkEquals equalsResultSort t1 =
    updateCallStack . checkSortsAgree mkEqualsWorker t1
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

-- | Construct an 'Exists' pattern.
mkExists ::
    HasCallStack =>
    InternalVariable variable =>
    ElementVariable variable ->
    Pattern variable ->
    Pattern variable
mkExists existsVariable existsChild =
    updateCallStack $
        synthesize (ExistsF Exists{existsSort, existsVariable, existsChild})
  where
    existsSort = patternSort existsChild

-- | Construct a sequence of 'Exists' patterns over several variables.
mkExistsN ::
    HasCallStack =>
    InternalVariable variable =>
    Foldable foldable =>
    foldable (ElementVariable variable) ->
    Pattern variable ->
    Pattern variable
mkExistsN = (updateCallStack .) . appEndo . foldMap (Endo . mkExists)

-- | Construct a 'Floor' pattern in the given sort.
mkFloor ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable ->
    Pattern variable
mkFloor floorResultSort floorChild =
    updateCallStack $
        synthesize (FloorF Floor{floorOperandSort, floorResultSort, floorChild})
  where
    floorOperandSort = patternSort floorChild

-- | Construct a 'Forall' pattern.
mkForall ::
    HasCallStack =>
    InternalVariable variable =>
    ElementVariable variable ->
    Pattern variable ->
    Pattern variable
mkForall forallVariable forallChild =
    updateCallStack $
        synthesize (ForallF Forall{forallSort, forallVariable, forallChild})
  where
    forallSort = patternSort forallChild

-- | Construct a sequence of 'Forall' patterns over several variables.
mkForallN ::
    HasCallStack =>
    InternalVariable variable =>
    Foldable foldable =>
    foldable (ElementVariable variable) ->
    Pattern variable ->
    Pattern variable
mkForallN = (updateCallStack .) . appEndo . foldMap (Endo . mkForall)

-- | Construct an 'Iff' pattern.
mkIff ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkIff t1 t2 = updateCallStack $ checkSortsAgree mkIffWorker t1 t2
  where
    mkIffWorker iffFirst iffSecond iffSort =
        synthesize (IffF Iff{iffSort, iffFirst, iffSecond})

-- | Construct an 'Implies' pattern.
mkImplies ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkImplies t1 t2 = updateCallStack $ checkSortsAgree mkImpliesWorker t1 t2
  where
    mkImpliesWorker impliesFirst impliesSecond impliesSort =
        synthesize (ImpliesF implies')
      where
        implies' = Implies{impliesSort, impliesFirst, impliesSecond}

{- | Construct a 'In' pattern in the given sort.

See also: 'mkIn_'
-}
mkIn ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkIn inResultSort t1 t2 = updateCallStack $ checkSortsAgree mkInWorker t1 t2
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

-- | Construct a 'Mu' pattern.
mkMu ::
    HasCallStack =>
    InternalVariable variable =>
    SetVariable variable ->
    Pattern variable ->
    Pattern variable
mkMu muVar = updateCallStack . checkSortsAgree mkMuWorker (mkSetVar muVar)
  where
    mkMuWorker (SetVar_ muVar') muChild _ =
        synthesize (MuF Mu{muVariable = muVar', muChild})
    mkMuWorker _ _ _ = error "Unreachable code"

-- | Construct a 'Next' pattern.
mkNext ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable
mkNext nextChild =
    updateCallStack $ synthesize (NextF Next{nextSort, nextChild})
  where
    nextSort = patternSort nextChild

-- | Construct a 'Not' pattern.
mkNot ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable
mkNot notChild =
    updateCallStack $ synthesize (NotF Not{notSort, notChild})
  where
    notSort = patternSort notChild

-- | Construct a 'Nu' pattern.
mkNu ::
    HasCallStack =>
    InternalVariable variable =>
    SetVariable variable ->
    Pattern variable ->
    Pattern variable
mkNu nuVar = updateCallStack . checkSortsAgree mkNuWorker (mkSetVar nuVar)
  where
    mkNuWorker (SetVar_ nuVar') nuChild _ =
        synthesize (NuF Nu{nuVariable = nuVar', nuChild})
    mkNuWorker _ _ _ = error "Unreachable code"

-- | Construct an 'Or' pattern.
mkOr ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkOr t1 t2 = updateCallStack $ checkSortsAgree mkOrWorker t1 t2
  where
    mkOrWorker orFirst orSecond orSort =
        synthesize (OrF Or{orSort, orFirst, orSecond})

-- | Construct a 'Rewrites' pattern.
mkRewrites ::
    HasCallStack =>
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable ->
    Pattern variable
mkRewrites t1 t2 = updateCallStack $ checkSortsAgree mkRewritesWorker t1 t2
  where
    mkRewritesWorker rewritesFirst rewritesSecond rewritesSort =
        synthesize (RewritesF rewrites')
      where
        rewrites' = Rewrites{rewritesSort, rewritesFirst, rewritesSecond}

{- | Construct a 'Top' pattern in the given sort.

See also: 'mkTop_'
-}
mkTop ::
    HasCallStack =>
    Ord variable =>
    Sort ->
    Pattern variable
mkTop topSort =
    updateCallStack $ synthesize (TopF Top{topSort})

-- | Construct an element variable pattern.
mkElemVar ::
    HasCallStack =>
    InternalVariable variable =>
    ElementVariable variable ->
    Pattern variable
mkElemVar = updateCallStack . mkVar . inject @(SomeVariable _)

-- | Construct a set variable pattern.
mkSetVar ::
    HasCallStack =>
    InternalVariable variable =>
    SetVariable variable ->
    Pattern variable
mkSetVar = updateCallStack . mkVar . inject @(SomeVariable _)

-- | Construct a 'StringLiteral' pattern.
mkStringLiteral ::
    HasCallStack =>
    InternalVariable variable =>
    Text ->
    Pattern variable
mkStringLiteral =
    updateCallStack . synthesize . StringLiteralF . Const . StringLiteral

mkInternalBytes ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    ByteString ->
    Pattern variable
mkInternalBytes sort value =
    updateCallStack . synthesize . InternalBytesF . Const $
        InternalBytes
            { internalBytesSort = sort
            , internalBytesValue = value
            }

mkInternalBytes' ::
    HasCallStack =>
    InternalVariable variable =>
    InternalBytes ->
    Pattern variable
mkInternalBytes' = updateCallStack . synthesize . InternalBytesF . Const

mkInhabitant ::
    HasCallStack =>
    InternalVariable variable =>
    Sort ->
    Pattern variable
mkInhabitant = updateCallStack . synthesize . InhabitantF . Inhabitant

-- | Construct an 'Endianness' pattern.
mkEndianness ::
    HasCallStack =>
    Ord variable =>
    Endianness ->
    Pattern variable
mkEndianness = updateCallStack . synthesize . EndiannessF . Const

-- | Construct an 'Signedness' pattern.
mkSignedness ::
    HasCallStack =>
    Ord variable =>
    Signedness ->
    Pattern variable
mkSignedness = updateCallStack . synthesize . SignednessF . Const

-- | Construct a variable pattern.
mkVar ::
    HasCallStack =>
    Ord variable =>
    SomeVariable variable ->
    Pattern variable
mkVar = updateCallStack . synthesize . VariableF . Const

mkSort :: Id -> Sort
mkSort name = SortActualSort $ SortActual name []

mkSortVariable :: Id -> Sort
mkSortVariable name = SortVariableSort $ SortVariable name

updateCallStack ::
    forall variable.
    HasCallStack =>
    Pattern variable ->
    Pattern variable
updateCallStack = Lens.set created callstack
  where
    created = _attributes . Lens.Product.field @"termCreated"
    callstack =
        Attribute.Created
            . Just
            . GHC.popCallStack
            . GHC.popCallStack
            $ GHC.callStack

    _attributes :: Lens' (Pattern variable) (PatternAttributes variable)
    _attributes =
        Lens.lens
            (\(Pattern (attrs :< _)) -> attrs)
            ( \(Pattern (_ :< termLikeF)) attrs ->
                Pattern (attrs :< termLikeF)
            )

checkSortsAgree ::
    (Pattern variable -> Pattern variable -> Sort -> a) ->
    Pattern variable ->
    Pattern variable ->
    a
checkSortsAgree withPatterns t1 t2 = withPatterns t1 t2 (sameSort s1 s2)
  where
    s1 = patternSort t1
    s2 = patternSort t2

{- | Force the 'Pattern's to conform to their 'Sort's.

It is an error if the lists are not the same length, or if any 'Pattern' cannot
be coerced to its corresponding 'Sort'.
-}
samePatternSorts ::
    HasCallStack =>
    InternalVariable variable =>
    [Sort] ->
    [Pattern variable] ->
    [Pattern variable]
samePatternSorts operandSorts children =
    alignWith forceTheseSorts operandSorts children
  where
    forceTheseSorts (This _) =
        (error . show . Pretty.vsep) ("Too few arguments:" : expected)
    forceTheseSorts (That _) =
        (error . show . Pretty.vsep) ("Too many arguments:" : expected)
    forceTheseSorts (These sort termLike) = samePatternSort sort termLike
    expected =
        [ "Expected:"
        , Pretty.indent 4 (Unparser.arguments operandSorts)
        , "but found:"
        , Pretty.indent 4 (Unparser.arguments children)
        ]

-- | Check the given `Pattern` has the same sort as that supplied
samePatternSort ::
    (InternalVariable variable, HasCallStack) =>
    -- | expected sort
    Sort ->
    Pattern variable ->
    Pattern variable
samePatternSort expectedSort term
    | expectedSort == termSort = term
    | otherwise = illSorted expectedSort term
  where
    termSort = patternSort term

illSorted ::
    (InternalVariable variable, HasCallStack) =>
    Sort ->
    Pattern variable ->
    a
illSorted forcedSort original =
    (error . show . Pretty.vsep)
        [ Pretty.cat
            [ "Could not force pattern to sort "
            , Pretty.squotes (unparse forcedSort)
            , ", instead it has sort "
            , Pretty.squotes (unparse (patternSort original))
            , ":"
            ]
        , Pretty.indent 4 (unparse original)
        ]

setSimplified ::
    (HasCallStack, InternalVariable variable) =>
    Attribute.Simplified ->
    Pattern variable ->
    Pattern variable
setSimplified
    simplified
    (Recursive.project -> attrs :< termLikeF) =
        Recursive.embed
            ( setAttributeSimplified mergedSimplified attrs
                :< termLikeF
            )
      where
        childSimplified = simplifiedFromChildren termLikeF
        mergedSimplified = case (childSimplified, simplified) of
            (Attribute.NotSimplified, Attribute.NotSimplified) ->
                Attribute.NotSimplified
            (Attribute.NotSimplified, _) ->
                cannotSimplifyNotSimplifiedError termLikeF
            (_, Attribute.NotSimplified) ->
                Attribute.NotSimplified
            _ -> childSimplified <> simplified

setAttributeSimplified ::
    Attribute.Simplified ->
    PatternAttributes variable ->
    PatternAttributes variable
setAttributeSimplified termSimplified attrs =
    attrs{termSimplified}

simplifiedFromChildren ::
    HasCallStack =>
    PatternF variable (Pattern variable) ->
    Attribute.Simplified
simplifiedFromChildren termLikeF =
    case mergedSimplified of
        Attribute.NotSimplified -> Attribute.NotSimplified
        _ -> mergedSimplified `Attribute.simplifiedTo` Attribute.fullySimplified
  where
    mergedSimplified =
        foldMap (attributeSimplifiedAttribute . extractAttributes) termLikeF

cannotSimplifyNotSimplifiedError ::
    (HasCallStack, InternalVariable variable) =>
    PatternF variable (Pattern variable) ->
    a
cannotSimplifyNotSimplifiedError termLikeF =
    error
        ( "Unexpectedly marking term with NotSimplified children as \
          \simplified:\n"
            ++ show termLikeF
            ++ "\n"
            ++ Unparser.unparseToString termLikeF
        )

data Modality = WEF | WAF

-- | Weak exists finally modality symbol.
weakExistsFinally :: Text
weakExistsFinally = "weakExistsFinally"

-- | Weak always finally modality symbol.
weakAlwaysFinally :: Text
weakAlwaysFinally = "weakAlwaysFinally"

-- | 'Alias' construct for weak exist finally.
wEF ::
    InternalVariable variable =>
    Sort ->
    Alias (Pattern variable)
wEF sort =
    Alias
        { aliasConstructor =
            Id
                { getId = weakExistsFinally
                , idLocation = AstLocationNone
                }
        , aliasParams = [sort]
        , aliasSorts =
            ApplicationSorts
                { applicationSortsOperands = [sort]
                , applicationSortsResult = sort
                }
        , aliasLeft = []
        , aliasRight = mkTop sort
        }

-- | 'Alias' construct for weak always finally.
wAF ::
    InternalVariable variable =>
    Sort ->
    Alias (Pattern variable)
wAF sort =
    Alias
        { aliasConstructor =
            Id
                { getId = weakAlwaysFinally
                , idLocation = AstLocationNone
                }
        , aliasParams = [sort]
        , aliasSorts =
            ApplicationSorts
                { applicationSortsOperands = [sort]
                , applicationSortsResult = sort
                }
        , aliasLeft = []
        , aliasRight = mkTop sort
        }

{- | Apply one of the reachability modality aliases
 to a term.
-}
applyModality ::
    InternalVariable variable =>
    Modality ->
    Pattern variable ->
    Pattern variable
applyModality modality term =
    case modality of
        WEF ->
            mkApplyAlias (wEF sort) [term]
        WAF ->
            mkApplyAlias (wAF sort) [term]
  where
    sort = patternSort term

-- TODO: this and Pattern.mapVariables should use the same code

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

See also: 'traverseVariables'
-}
mapVariables ::
    forall variable1 variable2.
    Ord variable1 =>
    FreshPartialOrd variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    Pattern variable1 ->
    Pattern variable2
mapVariables adj termLike =
    runIdentity (traverseVariables ((.) pure <$> adj) termLike)
{-# INLINE mapVariables #-}

{- | Use the provided traversal to replace all variables in a 'Pattern'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'
-}
traverseVariables ::
    forall variable1 variable2 m.
    Ord variable1 =>
    FreshPartialOrd variable2 =>
    Monad m =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    Pattern variable1 ->
    m (Pattern variable2)
traverseVariables adj termLike =
    renameFreeVariables
        adj
        (Attribute.freeVariables @_ @variable1 termLike)
        >>= Reader.runReaderT (Recursive.fold worker termLike)
  where
    adjReader = (.) lift <$> adj
    trElemVar = traverse $ traverseElementVariableName adjReader
    trSetVar = traverse $ traverseSetVariableName adjReader
    traverseExists avoiding =
        existsBinder (renameElementBinder trElemVar avoiding)
    traverseForall avoiding =
        forallBinder (renameElementBinder trElemVar avoiding)
    traverseMu avoiding =
        muBinder (renameSetBinder trSetVar avoiding)
    traverseNu avoiding =
        nuBinder (renameSetBinder trSetVar avoiding)

    worker ::
        Base
            (Pattern variable1)
            (RenamingT variable1 variable2 m (Pattern variable2)) ->
        RenamingT variable1 variable2 m (Pattern variable2)
    worker (attrs :< termLikeF) = do
        ~attrs' <- traverseAttributeVariables askSomeVariableName attrs
        let ~avoiding = Attribute.freeVariables attrs'
        termLikeF' <- case termLikeF of
            VariableF (Const unifiedVariable) -> do
                unifiedVariable' <- askSomeVariable unifiedVariable
                (pure . VariableF) (Const unifiedVariable')
            ExistsF exists -> ExistsF <$> traverseExists avoiding exists
            ForallF forall -> ForallF <$> traverseForall avoiding forall
            MuF mu -> MuF <$> traverseMu avoiding mu
            NuF nu -> NuF <$> traverseNu avoiding nu
            _ ->
                sequence termLikeF
                    >>=
                    -- traverseVariablesF will not actually call the traversals
                    -- because all the cases with variables are handled above.
                    traverseVariablesF askSomeVariableName
        (pure . Recursive.embed) (attrs' :< termLikeF')

{- | Use the provided traversal to replace the free variables in a 'PatternAttributes'.

See also: 'mapVariables'
-}
traverseAttributeVariables ::
    forall m variable1 variable2.
    Monad m =>
    Ord variable2 =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    PatternAttributes variable1 ->
    m (PatternAttributes variable2)
traverseAttributeVariables adj =
    Lens.Product.field @"termFreeVariables" (Attribute.traverseFreeVariables adj)

{- | Use the provided traversal to replace all variables in a 'PatternF' head.

__Warning__: @traverseVariablesF@ will capture variables if the provided
traversal is not injective!
-}
traverseVariablesF ::
    Applicative f =>
    AdjSomeVariableName (variable1 -> f variable2) ->
    PatternF variable1 child ->
    f (PatternF variable2 child)
traverseVariablesF adj =
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
        InternalBoolF boolP -> pure (InternalBoolF boolP)
        InternalBytesF bytesP -> pure (InternalBytesF bytesP)
        InternalIntF intP -> pure (InternalIntF intP)
        InternalStringF stringP -> pure (InternalStringF stringP)
        InternalListF listP -> pure (InternalListF listP)
        InternalMapF mapP -> pure (InternalMapF mapP)
        InternalSetF setP -> pure (InternalSetF setP)
        TopF topP -> pure (TopF topP)
        InhabitantF s -> pure (InhabitantF s)
        EndiannessF endianness -> pure (EndiannessF endianness)
        SignednessF signedness -> pure (SignednessF signedness)
        InjF inj -> pure (InjF inj)
  where
    trElemVar = traverse $ traverseElementVariableName adj
    trSetVar = traverse $ traverseSetVariableName adj
    traverseConstVariable (Const variable) =
        Const <$> traverseSomeVariable adj variable
    traverseVariablesExists Exists{existsSort, existsVariable, existsChild} =
        Exists existsSort
            <$> trElemVar existsVariable
            <*> pure existsChild
    traverseVariablesForall Forall{forallSort, forallVariable, forallChild} =
        Forall forallSort
            <$> trElemVar forallVariable
            <*> pure forallChild
    traverseVariablesMu Mu{muVariable, muChild} =
        Mu <$> trSetVar muVariable <*> pure muChild
    traverseVariablesNu Nu{nuVariable, nuChild} =
        Nu <$> trSetVar nuVariable <*> pure nuChild

instance InternalVariable variable => Substitute (Pattern variable) where
    type TermType (Pattern variable) = Pattern variable

    type VariableNameType (Pattern variable) = variable

    rename = substitute . fmap mkVar
    {-# INLINE rename #-}

    substitute = substituteWorker . Map.map Left
      where
        extractFreeVariables ::
            Pattern variable -> Set (SomeVariableName variable)
        extractFreeVariables = Attribute.toNames . Attribute.freeVariables

        getTargetFreeVariables ::
            Either (Pattern variable) (SomeVariable variable) ->
            Set (SomeVariableName variable)
        getTargetFreeVariables =
            either extractFreeVariables (Set.singleton . variableName)

        renaming ::
            -- | Original variable
            SomeVariable variable ->
            -- | Renamed variable
            Maybe (SomeVariable variable) ->
            -- | Substitution
            Map
                (SomeVariableName variable)
                (Either (Pattern variable) (SomeVariable variable)) ->
            Map
                (SomeVariableName variable)
                (Either (Pattern variable) (SomeVariable variable))
        renaming Variable{variableName} =
            maybe id (Map.insert variableName . Right)

        substituteWorker ::
            Map
                (SomeVariableName variable)
                (Either (Pattern variable) (SomeVariable variable)) ->
            Pattern variable ->
            Pattern variable
        substituteWorker subst termLike =
            substituteNone <|> substituteBinder <|> substituteVariable
                & fromMaybe substituteDefault
          where
            substituteNone :: Maybe (Pattern variable)
            substituteNone
                | Map.null subst' = pure termLike
                | otherwise = empty

            substituteBinder :: Maybe (Pattern variable)
            substituteBinder =
                runIdentity <$> matchWith traverseBinder worker termLike
              where
                worker ::
                    Binder (SomeVariable variable) (Pattern variable) ->
                    Identity (Binder (SomeVariable variable) (Pattern variable))
                worker Binder{binderVariable, binderChild} = do
                    let binderVariable' = avoidCapture binderVariable
                        -- Rename the freshened bound variable in the subterms.
                        subst'' = renaming binderVariable binderVariable' subst'
                    return
                        Binder
                            { binderVariable = fromMaybe binderVariable binderVariable'
                            , binderChild = substituteWorker subst'' binderChild
                            }

            substituteVariable :: Maybe (Pattern variable)
            substituteVariable =
                either id id <$> matchWith traverseVariable worker termLike
              where
                worker ::
                    SomeVariable variable ->
                    Either (Pattern variable) (SomeVariable variable)
                worker Variable{variableName} =
                    -- If the variable is not substituted or renamed, return the
                    -- original pattern.
                    fromMaybe
                        (Left termLike)
                        -- If the variable is renamed, 'Map.lookup' returns a
                        -- 'Right' which @traverseVariable@ embeds into
                        -- @patternType@. If the variable is substituted,
                        -- 'Map.lookup' returns a 'Left' which is used directly as
                        -- the result, exiting early from @traverseVariable@.
                        (Map.lookup variableName subst')

            substituteDefault =
                synthesize termLikeHead'
              where
                _ :< termLikeHead = Recursive.project termLike
                termLikeHead' = substituteWorker subst' <$> termLikeHead

            freeVars = extractFreeVariables termLike

            subst' = Map.intersection subst (Map.fromSet id freeVars)

            originalVariables = Set.difference freeVars (Map.keysSet subst')

            freeVariables' = Set.union originalVariables targetFreeVariables
              where
                targetFreeVariables =
                    foldl'
                        Set.union
                        Set.empty
                        (getTargetFreeVariables <$> subst')

            avoidCapture = refreshVariable freeVariables'

instance InternalVariable variable => Binding (Pattern variable) where
    type VariableType (Pattern variable) = variable

    traverseVariable traversal termLike =
        case termLikeF of
            VariableF (Const unifiedVariable) ->
                mkVar <$> traversal unifiedVariable
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

{- | Forget the 'simplifiedAttribute' associated with the 'Pattern.

@
isSimplified (forgetSimplified _) == False
@
-}
forgetSimplified ::
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable
forgetSimplified = resynthesize

{- | Is the 'Pattern' fully simplified under the given side condition?
-}
isSimplified :: SideCondition.Representation -> Pattern variable -> Bool
isSimplified sideCondition =
    isAttributeSimplified sideCondition . extractAttributes

{- Checks whether the pattern is simplified relative to the given side
condition.
-}
isAttributeSimplified ::
    HasCallStack =>
    SideCondition.Representation ->
    PatternAttributes variable ->
    Bool
isAttributeSimplified sideCondition patt@PatternAttributes{termSimplified} =
    assertSimplifiedConsistency patt $
        Attribute.isSimplified sideCondition termSimplified

-- | Construct an axiom declaration with the given parameters and pattern.
mkAxiom ::
    [SortVariable] ->
    Pattern variable ->
    SentenceAxiom (Pattern variable)
mkAxiom sentenceAxiomParameters sentenceAxiomPattern =
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes = Attributes []
        }
{- | Construct an axiom declaration with no parameters.

See also: 'mkAxiom'
-}
mkAxiom_ :: Pattern variable -> SentenceAxiom (Pattern variable)
mkAxiom_ = mkAxiom []

-- TODO: are these needed?
--
-- -- | Construct a symbol declaration with the given parameters and sorts.
-- mkSymbol ::
--     Id ->
--     [SortVariable] ->
--     [Sort] ->
--     Sort ->
--     SentenceSymbol
-- mkSymbol symbolConstructor symbolParams argumentSorts resultSort' =
--     SentenceSymbol
--         { sentenceSymbolSymbol =
--             Syntax.Symbol
--                 { symbolConstructor
--                 , symbolParams
--                 }
--         , sentenceSymbolSorts = argumentSorts
--         , sentenceSymbolResultSort = resultSort'
--         , sentenceSymbolAttributes = Attributes []
--         }
--
-- {- | Construct a symbol declaration with no parameters.
--
-- See also: 'mkSymbol'
-- -}
-- mkSymbol_ ::
--     Id ->
--     [Sort] ->
--     Sort ->
--     SentenceSymbol
-- mkSymbol_ symbolConstructor = mkSymbol symbolConstructor []
--
-- -- | Construct an alias declaration with the given parameters and sorts.
-- mkAlias ::
--     Id ->
--     [SortVariable] ->
--     Sort ->
--     [SomeVariable VariableName] ->
--     Pattern VariableName ->
--     SentenceAlias (Pattern VariableName)
-- mkAlias aliasConstructor aliasParams resultSort' arguments right =
--     SentenceAlias
--         { sentenceAliasAlias =
--             Syntax.Alias
--                 { aliasConstructor
--                 , aliasParams
--                 }
--         , sentenceAliasSorts = argumentSorts
--         , sentenceAliasResultSort = resultSort'
--         , sentenceAliasLeftPattern =
--             Application
--                 { applicationSymbolOrAlias =
--                     SymbolOrAlias
--                         { symbolOrAliasConstructor = aliasConstructor
--                         , symbolOrAliasParams =
--                             SortVariableSort <$> aliasParams
--                         }
--                 , applicationChildren = arguments
--                 }
--         , sentenceAliasRightPattern = right
--         , sentenceAliasAttributes = Attributes []
--         }
--   where
--     argumentSorts = variableSort <$> arguments
--
-- {- | Construct an alias declaration with no parameters.
--
-- See also: 'mkAlias'
-- -}
-- mkAlias_ ::
--     Id ->
--     Sort ->
--     [SomeVariable VariableName] ->
--     Pattern VariableName ->
--     SentenceAlias (Pattern VariableName)
-- mkAlias_ aliasConstructor = mkAlias aliasConstructor []
--
-- {- | Construct an 'Application' pattern from a 'Alias' declaration.
--
-- The provided sort parameters must match the declaration.
--
-- See also: 'mkApplyAlias', 'applyAlias_', 'applySymbol', 'mkAlias'
-- -}
-- applyAlias ::
--     HasCallStack =>
--     InternalVariable variable =>
--     -- | 'Alias' declaration
--     SentenceAlias (Pattern VariableName) ->
--     -- | 'Alias' sort parameters
--     [Sort] ->
--     -- | 'Application' arguments
--     [Pattern variable] ->
--     Pattern variable
-- applyAlias sentence params children =
--     updateCallStack $ mkApplyAlias internal children'
--   where
--     SentenceAlias{sentenceAliasAlias = external} = sentence
--     Syntax.Alias{aliasConstructor} = external
--     Syntax.Alias{aliasParams} = external
--     internal =
--         Alias
--             { aliasConstructor
--             , aliasParams = params
--             , aliasSorts =
--                 symbolOrAliasSorts params sentence
--                     & assertRight
--             , aliasLeft =
--                 applicationChildren
--                     . sentenceAliasLeftPattern
--                     $ sentence
--             , aliasRight = sentenceAliasRightPattern sentence
--             }
--     substitution = sortSubstitution aliasParams params
--     childSorts = substituteSortVariables substitution <$> sentenceAliasSorts
--       where
--         SentenceAlias{sentenceAliasSorts} = sentence
--     children' = alignWith forceChildSort childSorts children
--       where
--         forceChildSort =
--             \case
--                 These sort pattern' -> samePatternSort sort pattern'
--                 This _ ->
--                     (error . show . Pretty.vsep)
--                         ("Too few parameters:" : expected)
--                 That _ ->
--                     (error . show . Pretty.vsep)
--                         ("Too many parameters:" : expected)
--         expected =
--             [ "Expected:"
--             , Pretty.indent 4 (Unparser.arguments childSorts)
--             , "but found:"
--             , Pretty.indent 4 (Unparser.arguments children)
--             ]
--
-- {- | Construct an 'Application' pattern from a 'Alias' declaration.
--
-- The 'Alias' must not be declared with sort parameters.
--
-- See also: 'mkApp', 'applyAlias'
-- -}
-- applyAlias_ ::
--     HasCallStack =>
--     InternalVariable variable =>
--     SentenceAlias (Pattern VariableName) ->
--     [Pattern variable] ->
--     Pattern variable
-- applyAlias_ sentence = updateCallStack . applyAlias sentence []
--
