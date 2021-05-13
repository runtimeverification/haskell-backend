{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2020
License     : NCSA
-}
module Kore.Internal.TermLike.TermLike (
    TermLike (..),
    TermLikeF (..),
    TermAttributes (..),
    freeVariables,
    retractKey,
    extractAttributes,
    mapVariables,
    traverseVariables,
    mkVar,
    traverseVariablesF,
    updateCallStack,
    depth,
    isAttributeSimplified,
    isAttributeSimplifiedAnyCondition,
    isAttributeSimplifiedSomeCondition,
    attributeSimplifiedAttribute,
    setAttributeSimplified,
    mapAttributeVariables,
    deleteFreeVariable,
) where

import Control.Comonad.Trans.Cofree (
    tailF,
 )
import Control.Lens (
    Lens',
 )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import qualified Control.Monad.Reader as Reader
import Data.Functor.Const (
    Const (..),
 )
import Data.Functor.Foldable (
    Base,
    Corecursive,
    Recursive,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity (
    Identity (..),
 )
import Data.Generics.Product
import qualified Data.Generics.Product as Lens.Product
import Data.HashSet (
    HashSet,
 )
import qualified Data.HashSet as HashSet
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC
import qualified Generics.SOP as SOP
import Kore.AST.AstWithLocation
import qualified Kore.Attribute.Pattern.ConstructorLike as Attribute
import qualified Kore.Attribute.Pattern.Created as Attribute
import qualified Kore.Attribute.Pattern.Defined as Attribute
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (..),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute.FreeVariables
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
    KeyAttributes (KeyAttributes),
    KeyF,
 )
import qualified Kore.Internal.Key as Attribute
import qualified Kore.Internal.Key as Key
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import Kore.Internal.Symbol (
    Symbol,
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
import Kore.TopBottom
import Kore.Unparser (
    Unparse (..),
 )
import qualified Kore.Unparser as Unparser
import Kore.Variables.Binding
import Prelude.Kore
import qualified Pretty
import qualified SQL

-- | 'TermLikeF' is the 'Base' functor of internal term-like patterns.
data TermLikeF variable child
    = AndF !(And Sort child)
    | ApplySymbolF !(Application Symbol child)
    | -- TODO (thomas.tuegel): Expand aliases during validation?
      ApplyAliasF !(Application (Alias (TermLike VariableName)) child)
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

instance (Unparse variable, Unparse child) => Unparse (TermLikeF variable child) where
    unparse = Unparser.unparseGeneric
    unparse2 = Unparser.unparse2Generic

instance
    Ord variable =>
    Synthetic (Attribute.FreeVariables variable) (TermLikeF variable)
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

instance Synthetic Sort (TermLikeF variable) where
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

instance Synthetic Attribute.Functional (TermLikeF variable) where
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

instance Synthetic Attribute.Function (TermLikeF variable) where
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

instance Synthetic Attribute.Defined (TermLikeF variable) where
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

instance Synthetic Attribute.Simplified (TermLikeF variable) where
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

instance Synthetic Attribute.ConstructorLike (TermLikeF variable) where
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

instance From (KeyF child) (TermLikeF variable child) where
    from (Key.ApplySymbolF app) = ApplySymbolF app
    from (Key.InjF inj) = InjF inj
    from (Key.DomainValueF domainValue) = DomainValueF domainValue
    from (Key.InternalBoolF internalBool) = InternalBoolF internalBool
    from (Key.InternalIntF internalInt) = InternalIntF internalInt
    from (Key.InternalStringF internalString) = InternalStringF internalString
    from (Key.InternalSetF internalSet) = InternalSetF internalSet
    from (Key.InternalMapF internalMap) = InternalMapF internalMap
    from (Key.InternalListF internalList) = InternalListF internalList
    from (Key.InternalBytesF internalBytes) = InternalBytesF internalBytes
    from (Key.StringLiteralF stringLiteral) = StringLiteralF stringLiteral
    {-# INLINE from #-}

-- | @TermAttributes@ are the attributes of a pattern collected during verification.
data TermAttributes variable = TermAttributes
    { termSort :: !Sort
    , termFreeVariables :: !(Attribute.FreeVariables variable)
    , termFunctional :: !Attribute.Functional
    , termFunction :: !Attribute.Function
    , termDefined :: !Attribute.Defined
    , termCreated :: !Attribute.Created
    , termSimplified :: !Attribute.Simplified
    , termConstructorLike :: !Attribute.ConstructorLike
    , termSubterms :: !(Subterms variable)
    }
    deriving stock (Eq, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Debug variable => Debug (TermAttributes variable) where
    debugPrecBrief _ _ = "_"

instance (Debug variable, Diff variable) => Diff (TermAttributes variable)

instance
    ( Ord variable
    , Hashable variable
    ) =>
    Synthetic (TermAttributes variable) (TermLikeF variable)
    where
    synthetic base =
        let ~attrs =
                TermAttributes
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
                    , termSubterms =
                        Subterms
                            { term = term'
                            , subterms = subterms'
                            }
                    }
            term' = Recursive.embed (attrs :< (term . termSubterms <$> base))
            subterms' = HashSet.insert term' (foldMap (subterms . termSubterms) base)
         in attrs
      where
        constructorLikeAttr :: Attribute.ConstructorLike
        constructorLikeAttr = synthetic (termConstructorLike <$> base)

instance Attribute.HasConstructorLike (TermAttributes variable) where
    extractConstructorLike
        TermAttributes{termConstructorLike} =
            termConstructorLike

instance (Ord variable) => From KeyAttributes (TermAttributes variable) where
    from = fromKeyAttributes

attributeSimplifiedAttribute ::
    HasCallStack =>
    TermAttributes variable ->
    Attribute.Simplified
attributeSimplifiedAttribute patt@TermAttributes{termSimplified} =
    assertSimplifiedConsistency patt termSimplified

constructorLikeAttribute ::
    TermAttributes variable ->
    Attribute.ConstructorLike
constructorLikeAttribute TermAttributes{termConstructorLike} =
    termConstructorLike

{- Checks whether the pattern is simplified relative to the given side
condition.
-}
isAttributeSimplified ::
    HasCallStack =>
    SideCondition.Representation ->
    TermAttributes variable ->
    Bool
isAttributeSimplified sideCondition patt@TermAttributes{termSimplified} =
    assertSimplifiedConsistency patt $
        Attribute.isSimplified sideCondition termSimplified

{- Checks whether the pattern is simplified relative to some side condition.
-}
isAttributeSimplifiedSomeCondition ::
    HasCallStack =>
    TermAttributes variable ->
    Bool
isAttributeSimplifiedSomeCondition patt@TermAttributes{termSimplified} =
    assertSimplifiedConsistency patt $
        Attribute.isSimplifiedSomeCondition termSimplified

{- Checks whether the pattern is simplified relative to any side condition.
-}
isAttributeSimplifiedAnyCondition ::
    HasCallStack =>
    TermAttributes variable ->
    Bool
isAttributeSimplifiedAnyCondition patt@TermAttributes{termSimplified} =
    assertSimplifiedConsistency patt $
        Attribute.isSimplifiedAnyCondition termSimplified

assertSimplifiedConsistency :: HasCallStack => TermAttributes variable -> a -> a
assertSimplifiedConsistency
    TermAttributes{termConstructorLike, termSimplified}
        | Attribute.isConstructorLike termConstructorLike
          , not (Attribute.isSimplifiedAnyCondition termSimplified) =
            error "Inconsistent attributes, constructorLike implies fully simplified."
        | otherwise = id

setAttributeSimplified ::
    Attribute.Simplified ->
    TermAttributes variable ->
    TermAttributes variable
setAttributeSimplified termSimplified attrs =
    attrs{termSimplified}

-- TODO: should we remove this? it isn't used anywhere

{- | Use the provided mapping to replace all variables in a 'TermAttributes'.

See also: 'traverseVariables'
-}
mapAttributeVariables ::
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    TermAttributes variable1 ->
    TermAttributes variable2
mapAttributeVariables adj termAttributes =
    termAttributes
        { termFreeVariables =
            Attribute.mapFreeVariables adj (termFreeVariables termAttributes)
        , termSubterms =
            mapSubterms adj (termSubterms termAttributes)
        }

{- | Use the provided traversal to replace the free variables in a 'TermAttributes'.

See also: 'mapVariables'
-}
traverseAttributeVariables ::
    forall m variable1 variable2.
    Monad m =>
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    TermAttributes variable1 ->
    m (TermAttributes variable2)
traverseAttributeVariables
    adj
    termAttributes@TermAttributes
        { termFreeVariables
        , termSubterms
        } =
        do
            freeVariables' <- Attribute.traverseFreeVariables adj termFreeVariables
            subterms' <- traverseSubterms adj termSubterms
            return
                termAttributes
                    { termFreeVariables = freeVariables'
                    , termSubterms = subterms'
                    }

-- TODO: should we remove this? it isn't used anywhere

-- | Delete the given variable from the set of free variables.
deleteFreeVariable ::
    Ord variable =>
    SomeVariable variable ->
    TermAttributes variable ->
    TermAttributes variable
deleteFreeVariable variable =
    Lens.over
        (field @"termFreeVariables")
        (Attribute.FreeVariables.bindVariable variable)

instance HasFreeVariables (TermAttributes variable) variable where
    freeVariables = termFreeVariables

{- | @TermLike@ is a term-like Kore pattern.

@TermLike@ is the common internal representation of patterns, especially terms.

@TermLike@ is essentially 'Control.Comonad.Cofree.Cofree', but rather than
define a @newtype@ over @Cofree@, it is defined inline for performance. The
performance advantage owes to the fact that the instances of 'Recursive.project'
and 'Recursive.embed' correspond to unwrapping and wrapping the @newtype@,
respectively, which is free at runtime.
-}
newtype TermLike variable = TermLike
    { getTermLike ::
        CofreeF
            (TermLikeF variable)
            (TermAttributes variable)
            (TermLike variable)
    }
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

instance (Debug variable, Diff variable) => Diff (TermLike variable) where
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
    (Eq variable, Eq (TermLikeF variable (TermLike variable))) =>
    Eq (TermLike variable)
    where
    (==)
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2) =
            pat1 == pat2

instance
    (Ord variable, Ord (TermLikeF variable (TermLike variable))) =>
    Ord (TermLike variable)
    where
    compare
        (Recursive.project -> _ :< pat1)
        (Recursive.project -> _ :< pat2) =
            compare pat1 pat2

instance Hashable variable => Hashable (TermLike variable) where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat
    {-# INLINE hashWithSalt #-}

instance NFData variable => NFData (TermLike variable) where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat

instance (Unparse variable, Ord variable) => Unparse (TermLike variable) where
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
                TermAttributes{termCreated} = attrs

                attributeRepresentation = case attrs of
                    (TermAttributes _ _ _ _ _ _ _ _ _) ->
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

type instance
    Base (TermLike variable) =
        CofreeF (TermLikeF variable) (TermAttributes variable)

-- This instance implements all class functions for the TermLike newtype
-- because the their implementations for the inner type may be specialized.
instance Recursive (TermLike variable) where
    project = getTermLike
    {-# INLINE project #-}

-- This instance implements all class functions for the TermLike newtype
-- because the their implementations for the inner type may be specialized.
instance Corecursive (TermLike variable) where
    embed = TermLike
    {-# INLINE embed #-}

instance TopBottom (TermLike variable) where
    isTop (Recursive.project -> _ :< TopF Top{}) = True
    isTop _ = False
    isBottom (Recursive.project -> _ :< BottomF Bottom{}) = True
    isBottom _ = False

instance InternalVariable variable => Binding (TermLike variable) where
    type VariableType (TermLike variable) = variable

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

instance Attribute.HasConstructorLike (TermLike variable) where
    extractConstructorLike (Recursive.project -> attrs :< _) =
        Attribute.extractConstructorLike attrs

instance Unparse (TermLike variable) => SQL.Column (TermLike variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

instance
    (InternalVariable variable) =>
    From (TermLike Concrete) (TermLike variable)
    where
    from = mapVariables (pure $ from @Concrete)
    {-# INLINE from #-}

instance Ord variable => From Key (TermLike variable) where
    from = Recursive.unfold worker
      where
        worker key =
            attrs' :< from @(KeyF _) keyF
          where
            attrs :< keyF = Recursive.project key
            attrs' = fromKeyAttributes attrs

-- TODO: make From isntance
fromKeyAttributes ::
    Ord variable =>
    KeyAttributes ->
    TermAttributes variable
fromKeyAttributes attrs =
    TermAttributes
        { termSort = Attribute.keySort attrs
        , termFreeVariables = mempty
        , termFunctional = Attribute.Functional True
        , termFunction = Attribute.Function True
        , termDefined = Attribute.Defined True
        , termSimplified = Attribute.fullySimplified
        , termConstructorLike =
            Attribute.ConstructorLike (Just Attribute.ConstructorLikeHead)
        , termCreated = Attribute.Created Nothing
        , termSubterms = undefined
        }

toKeyAttributes :: TermAttributes variable -> Maybe KeyAttributes
toKeyAttributes attrs@(TermAttributes _ _ _ _ _ _ _ _ _)
    | Attribute.nullFreeVariables termFreeVariables
      , Attribute.isFunctional termFunctional
      , Attribute.isFunction termFunction
      , Attribute.isDefined termDefined
      , Attribute.isSimplifiedAnyCondition termSimplified
      , Attribute.isConstructorLike termConstructorLike =
        Just $ KeyAttributes termSort
    | otherwise = Nothing
  where
    TermAttributes
        { termSort
        , termFreeVariables
        , termFunctional
        , termFunction
        , termDefined
        , termConstructorLike
        , termSimplified
        } = attrs

-- | Ensure that a 'TermLike' is a concrete, constructor-like term.
retractKey :: TermLike variable -> Maybe Key
retractKey =
    Recursive.fold worker
  where
    worker (attrs :< termLikeF) = do
        Monad.guard (Attribute.isConstructorLike attrs)
        attrs' <- toKeyAttributes attrs
        keyF <-
            case termLikeF of
                InternalBoolF internalBool ->
                    sequence (Key.InternalBoolF internalBool)
                InternalBytesF internalBytes ->
                    sequence (Key.InternalBytesF internalBytes)
                InternalIntF internalInt ->
                    sequence (Key.InternalIntF internalInt)
                InternalStringF internalString ->
                    sequence (Key.InternalStringF internalString)
                DomainValueF domainValue ->
                    sequence (Key.DomainValueF domainValue)
                InjF inj ->
                    sequence (Key.InjF inj)
                ApplySymbolF application ->
                    sequence (Key.ApplySymbolF application)
                InternalListF internalList ->
                    sequence (Key.InternalListF internalList)
                InternalMapF internalMap ->
                    sequence (Key.InternalMapF internalMap)
                InternalSetF internalSet ->
                    sequence (Key.InternalSetF internalSet)
                StringLiteralF stringLiteral ->
                    sequence (Key.StringLiteralF stringLiteral)
                _ -> empty
        pure (Recursive.embed (attrs' :< keyF))

instance
    ( AstWithLocation variable
    , AstWithLocation child
    ) =>
    AstWithLocation (TermLikeF variable child)
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

instance AstWithLocation variable => AstWithLocation (TermLike variable) where
    locationFromAst = locationFromAst . tailF . Recursive.project

{- | Use the provided traversal to replace all variables in a 'TermLikeF' head.

__Warning__: @traverseVariablesF@ will capture variables if the provided
traversal is not injective!
-}
traverseVariablesF ::
    Applicative f =>
    AdjSomeVariableName (variable1 -> f variable2) ->
    TermLikeF variable1 child ->
    f (TermLikeF variable2 child)
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

extractAttributes :: TermLike variable -> TermAttributes variable
extractAttributes (TermLike (attrs :< _)) = attrs

instance HasFreeVariables (TermLike variable) variable where
    freeVariables = Attribute.freeVariables . extractAttributes

{- | Use the provided mapping to replace all variables in a 'StepPattern'.

@mapVariables@ is lazy: it descends into its argument only as the result is
demanded. Intermediate allocation from composing multiple transformations with
@mapVariables@ is amortized; the intermediate trees are never fully resident.

See also: 'traverseVariables'
-}
mapVariables ::
    forall variable1 variable2.
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    TermLike variable1 ->
    TermLike variable2
mapVariables adj termLike =
    runIdentity (traverseVariables ((.) pure <$> adj) termLike)
{-# INLINE mapVariables #-}

{- | Use the provided traversal to replace all variables in a 'TermLike'.

@traverseVariables@ is strict, i.e. its argument is fully evaluated before it
returns. When composing multiple transformations with @traverseVariables@, the
intermediate trees will be fully allocated; @mapVariables@ is more composable in
this respect.

See also: 'mapVariables'
-}
traverseVariables ::
    forall variable1 variable2 m.
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    Monad m =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    TermLike variable1 ->
    m (TermLike variable2)
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
            (TermLike variable1)
            (RenamingT variable1 variable2 m (TermLike variable2)) ->
        RenamingT variable1 variable2 m (TermLike variable2)
    worker (attrs :< termLikeF) = do
        ~attrs' <- traverseAttributeVariables askSomeVariableName attrs
        let ~avoiding = freeVariables attrs'
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

updateCallStack ::
    forall variable.
    HasCallStack =>
    TermLike variable ->
    TermLike variable
updateCallStack = Lens.set created callstack
  where
    created = _attributes . Lens.Product.field @"termCreated"
    callstack =
        Attribute.Created
            . Just
            . GHC.popCallStack
            . GHC.popCallStack
            $ GHC.callStack

    _attributes :: Lens' (TermLike variable) (TermAttributes variable)
    _attributes =
        Lens.lens
            (\(TermLike (attrs :< _)) -> attrs)
            ( \(TermLike (_ :< termLikeF)) attrs ->
                TermLike (attrs :< termLikeF)
            )

-- | Construct a variable pattern.
mkVar ::
    HasCallStack =>
    Ord variable =>
    Hashable variable =>
    SomeVariable variable ->
    TermLike variable
mkVar = updateCallStack . synthesize . VariableF . Const

depth :: TermLike variable -> Int
depth = Recursive.fold levelDepth
  where
    levelDepth (_ :< termF) = 1 + foldl' max 0 termF

-- | An attribute type for caching the sub-terms of a term.
data Subterms variable = Subterms
    { subterms :: !(HashSet (TermLike variable))
    , term :: !(TermLike variable)
    }
    deriving stock (Eq, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (Debug, Diff)

mapSubterms ::
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    Subterms variable1 ->
    Subterms variable2
mapSubterms adj subtermsAttr =
    let subterms' =
            HashSet.map (mapVariables adj) (subterms subtermsAttr)
        term' = mapVariables adj (term subtermsAttr)
     in subtermsAttr{term = term', subterms = subterms'}

traverseSubterms ::
    Monad m =>
    InternalVariable variable1 =>
    InternalVariable variable2 =>
    AdjSomeVariableName (variable1 -> m variable2) ->
    Subterms variable1 ->
    m (Subterms variable2)
traverseSubterms adj subtermsAttr = do
    let subtermsList = HashSet.toList (subterms subtermsAttr)
    subterms' <-
        traverse (traverseVariables adj) subtermsList
            & fmap HashSet.fromList
    term' <-
        traverseVariables adj (term subtermsAttr)
    return subtermsAttr{term = term', subterms = subterms'}
