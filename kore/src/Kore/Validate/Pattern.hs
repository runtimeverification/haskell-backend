{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Validate.Pattern (
    Pattern,
    PatternF (..),
    extractAttributes,
    patternSort,

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
import Data.Text (Text)
import qualified GHC.Generics as GHC
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
import Kore.TopBottom
import Kore.Unparser (Unparse (..))
import qualified Kore.Unparser as Unparser
import Prelude.Kore
import qualified Pretty

-- | 'PatternF' is the 'Base' functor of validated patterns.
data PatternF variable child
    = AndF !(And Sort child)
    | ApplySymbolF !(Application Symbol child)
    | -- TODO (thomas.tuegel): Expand aliases during validation?
      ApplyAliasF !(Application (Alias (Pattern variable)) child)
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
    deriving stock (Show)
    deriving stock (Foldable, Functor, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

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

-- TODO: can this and TermLike's instance be factored out?
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
    Alias (Pattern variable) ->
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
