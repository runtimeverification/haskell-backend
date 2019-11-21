{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiableF (..)
    , FullySimplified (..)
    , SimplifiedChildren (..)

    , freeVariables
    , substitute

    -- * Constructors
    , bottom
    , top
    , fromCondition
    , fromMultiAnd
    , fromMultiOr
    , fromOrCondition
    , fromOrPattern
    , fromPattern
    , fromPredicate
    , fromTermLike
    -- Do not use outside Or simplification. Use fromOrPattern.
    , onlyForOrSimplified
    --
    , termFSimplifiableFromOrPattern
    --
    -- Use with qualified import:
    -- import qualified Kore.Step.Simplification.Simplifiable as Unsimplified
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
    , mkEvaluated
    , mkExists
    , mkFloor
    , mkForall
    , mkIff
    , mkImplies
    , mkIn
    , mkInhabitant
    , mkInternalBytes
    , mkMu
    , mkNext
    , mkNot
    , mkNu
    , mkOr
    , mkRewrites
    , mkStringLiteral
    , mkTop
    , mkElemVar
    , mkSetVar
    , mkVar
    ) where

import Control.Applicative
    ( Const (Const)
    )
import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import Data.ByteString
    ( ByteString
    )
import qualified Data.Foldable as Foldable
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.List
    ( foldl'
    )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Pattern as Attribute
    ( Pattern (Pattern)
    )
import qualified Kore.Attribute.Pattern as Attribute.DoNotUse
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute
    ( FreeVariables (FreeVariables)
    )
import qualified Kore.Attribute.Pattern.Simplified as Attribute
    ( Simplified (Simplified)
    )
import qualified Kore.Domain.Builtin as Domain
    ( Builtin (..)
    , InternalList
    , InternalMap
    , InternalSet
    )
import Kore.Internal.Alias
    ( Alias
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
    ( fromPredicate
    , isSimplified
    )
import Kore.Internal.InternalBytes
    ( InternalBytes (InternalBytes)
    )
import qualified Kore.Internal.InternalBytes as InternalBytes.DoNotUse
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
    )
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
    ( bottom
    , fromPattern
    , fromTermLike
    , isSimplified
    , toPatterns
    , toTermLike
    , top
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromCondition
    , isSimplified
    , toTermLike
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
    ( makePredicate
    )
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( Evaluated (Evaluated)
    , TermLike
    , TermLikeF (..)
    )
import qualified Kore.Internal.TermLike as TermLike
    ( freeVariables
    , substitute
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Sort
    ( Sort
    , predicateSort
    )
import qualified Kore.Substitute as Substitute
    ( SubstitutionVariable
    )
import Kore.Syntax.And
    ( And (And)
    )
import qualified Kore.Syntax.And as And.DoNotUse
import Kore.Syntax.Application
    ( Application (Application)
    )
import qualified Kore.Syntax.Application as Application.DoNotUse
import Kore.Syntax.Bottom
    ( Bottom (Bottom)
    )
import qualified Kore.Syntax.Bottom as Bottom.DoNotUse
import Kore.Syntax.Ceil
    ( Ceil (Ceil)
    )
import qualified Kore.Syntax.Ceil as Ceil.DoNotUse
import Kore.Syntax.DomainValue
    ( DomainValue
    )
import Kore.Syntax.ElementVariable
    ( ElementVariable
    )
import Kore.Syntax.Equals
    ( Equals (Equals)
    )
import qualified Kore.Syntax.Equals as Equals.DoNotUse
import Kore.Syntax.Exists
    ( Exists (Exists)
    )
import qualified Kore.Syntax.Exists as Exists.DoNotUse
import Kore.Syntax.Floor
    ( Floor (Floor)
    )
import qualified Kore.Syntax.Floor as Floor.DoNotUse
import Kore.Syntax.Forall
    ( Forall (Forall)
    )
import qualified Kore.Syntax.Forall as Forall.DoNotUse
import Kore.Syntax.Iff
    ( Iff (Iff)
    )
import qualified Kore.Syntax.Iff as Iff.DoNotUse
import Kore.Syntax.Implies
    ( Implies (Implies)
    )
import qualified Kore.Syntax.Implies as Implies.DoNotUse
import Kore.Syntax.In
    ( In (In)
    )
import qualified Kore.Syntax.In as In.DoNotUse
import Kore.Syntax.Inhabitant
    ( Inhabitant (Inhabitant)
    )
import Kore.Syntax.Mu
    ( Mu (Mu)
    )
import qualified Kore.Syntax.Mu as Mu.DoNotUse
import Kore.Syntax.Next
    ( Next (Next)
    )
import qualified Kore.Syntax.Next as Next.DoNotUse
import Kore.Syntax.Not
    ( Not (Not)
    )
import qualified Kore.Syntax.Not as Not.DoNotUse
import Kore.Syntax.Nu
    ( Nu (Nu)
    )
import qualified Kore.Syntax.Nu as Nu.DoNotUse
import Kore.Syntax.Or
    ( Or (Or)
    )
import qualified Kore.Syntax.Or as Or.DoNotUse
import Kore.Syntax.Rewrites
    ( Rewrites (Rewrites)
    )
import qualified Kore.Syntax.Rewrites as Rewrites.DoNotUse
import Kore.Syntax.SetVariable
    ( SetVariable
    )
import Kore.Syntax.StringLiteral
    ( StringLiteral (StringLiteral)
    )
import Kore.Syntax.Top
    ( Top (Top)
    )
import qualified Kore.Syntax.Top as Top.DoNotUse
import Kore.Syntax.Variable
    ( Concrete
    , Variable
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( unparseToString
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

newtype FullySimplified variable =
    FullySimplified { getFullySimplified :: OrPattern variable }

newtype SimplifiedChildren variable =
    SimplifiedChildren { getSimplifiedChildren :: OrPattern variable }

data SimplifiableF variable child
    = Simplified (OrPattern variable)
    | PartlySimplified (OrPattern variable)
    | Unsimplified (TermLikeF variable child)
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

newtype Simplifiable variable = Simplifiable
    { getSimplifiable :: Recursive.Fix (SimplifiableF variable) }
    deriving (GHC.Generic)

instance Ord variable => Eq (Simplifiable variable)
  where
    (==)
        (Recursive.project -> first)
        (Recursive.project -> second)
      =
        first == second

instance Ord variable => Ord (Simplifiable variable) where
    compare
        (Recursive.project -> first)
        (Recursive.project -> second)
      =
        compare first second

instance Show variable => Show (Simplifiable variable) where
    showsPrec prec (Recursive.project -> simplifiable) =
        showParen (prec >= 10)
        $ showString "Simplifiable "
        . showParen True
            ( showString "Fix "
            . showsPrec 10 simplifiable
            )

type instance Base (Simplifiable variable) = SimplifiableF variable

instance Recursive (Simplifiable variable) where
    project (Simplifiable (Recursive.Fix embedded)) = Simplifiable <$> embedded
instance Corecursive (Simplifiable variable) where
    embed projected =
        Simplifiable $ Recursive.Fix (getSimplifiable <$> projected)

instance TopBottom (Simplifiable variable) where
    isTop (Recursive.project -> simplifiable) =
        case simplifiable of
            Simplified orPatt -> isTop orPatt
            Unsimplified (TopF _) ->  True
            _ -> False
    isBottom (Recursive.project -> simplifiable) =
        case simplifiable of
            Simplified orPatt -> isBottom orPatt
            Unsimplified (BottomF _) -> True
            _ -> False

{-| Do not use outside Or simplification. Use fromOrPattern et co instead.
-}
onlyForOrSimplified :: OrPattern variable -> Simplifiable variable
onlyForOrSimplified = simplified

simplified :: OrPattern variable -> Simplifiable variable
simplified = Recursive.embed . Simplified . assertSimplified
  where
    assertSimplified orPatt =
        if OrPattern.isSimplified orPatt
            then orPatt
            else error "Expected simplified or."

partlySimplified :: OrPattern variable -> Simplifiable variable
partlySimplified = Recursive.embed . Simplified . assertSimplified
  where
    assertSimplified orPatt =
        if OrPattern.isSimplified orPatt
            then orPatt
            else error "Expected simplified or."

unsimplified
    :: TermLikeF variable (Simplifiable variable) -> Simplifiable variable
unsimplified = Recursive.embed . Unsimplified

fromTermLike
    :: forall variable
    .   InternalVariable variable
    => TermLike variable -> Simplifiable variable
fromTermLike =
    Recursive.elgot fromTermLikeBottomUp fromTermLikeTopDown
  where
    fromTermLikeBottomUp
        :: Recursive.Base (TermLike variable) (Simplifiable variable)
        -> Simplifiable variable
    fromTermLikeBottomUp (_ :< termF) = unsimplified termF

    fromTermLikeTopDown
        :: TermLike variable
        -> Either
            (Simplifiable variable)
            (Recursive.Base (TermLike variable) (TermLike variable))
    fromTermLikeTopDown term =
        case Recursive.project term of
            base@(attrs :< _) -> if alreadySimplified attrs
                then
                    let orPatt = case Predicate.makePredicate term of
                            Left _ -> OrPattern.fromTermLike term
                            Right termPredicate ->
                                OrPattern.fromPattern
                                $ Pattern.fromCondition
                                $ assertConditionSimplified term
                                $ Condition.fromPredicate termPredicate
                    in Left (simplified orPatt)
                else Right base
      where
        alreadySimplified
            Attribute.Pattern {simplified = Attribute.Simplified {isSimplified}}
          = isSimplified

        assertConditionSimplified
            :: TermLike variable -> Condition variable -> Condition variable
        assertConditionSimplified originalTerm condition =
            if Condition.isSimplified condition
                then condition
                else (error . unlines)
                    [ "Not simplified."
                    , "term = "
                    , unparseToString originalTerm
                    , "condition = "
                    , unparseToString condition
                    ]

fromOrPattern
    :: InternalVariable variable
    => OrPattern variable -> Simplifiable variable
fromOrPattern orPattern =
    case OrPattern.toPatterns orPattern of
        [] -> simplified orPattern
        [patt]
          | Pattern.isSimplified patt -> simplified orPattern
        _
          | OrPattern.isSimplified orPattern ->
            partlySimplified orPattern
          | otherwise ->
            fromMultiOr (fromPattern <$> orPattern)

fromOrCondition
    :: InternalVariable variable
    => OrCondition variable -> Simplifiable variable
fromOrCondition orCondition =
    fromOrPattern (Pattern.fromCondition <$> orCondition)

fromPattern
    :: InternalVariable variable
    => Pattern variable -> Simplifiable variable
fromPattern patt
  | Pattern.isSimplified patt = simplified (OrPattern.fromPattern patt)
  | otherwise = fromTermLike (Pattern.toTermLike patt)

fromCondition
    :: InternalVariable variable
    => Condition variable
    -> Simplifiable variable
fromCondition = fromPattern . Pattern.fromCondition

fromPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Simplifiable variable
fromPredicate = fromCondition . Condition.fromPredicate

termFSimplifiableFromOrPattern
    :: InternalVariable variable
    => OrPattern variable
    -> TermLikeF variable (Simplifiable variable)
termFSimplifiableFromOrPattern =
    foldl' mkOrFF mkBottomF . OrPattern.toPatterns
  where
    mkOrFF termF patt = mkOrF (unsimplified termF) (fromPattern patt)

top :: InternalVariable variable => Simplifiable variable
top = simplified OrPattern.top

bottom :: InternalVariable variable => Simplifiable variable
bottom = simplified OrPattern.bottom

fromMultiAnd
    :: InternalVariable variable
    => MultiAnd (Simplifiable variable)
    -> Simplifiable variable
fromMultiAnd andPatt =
    case MultiAnd.extractPatterns andPatt of
        [] -> simplified OrPattern.top
        (patt : patterns) -> foldl' mkAnd patt patterns

fromMultiOr
    :: InternalVariable variable
    => MultiOr (Simplifiable variable)
    -> Simplifiable variable
fromMultiOr orPatt =
    case MultiOr.extractPatterns orPatt of
        [] -> simplified OrPattern.bottom
        (patt : patterns) -> foldl' mkOr patt patterns

mkAnd :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkAnd andFirst andSecond =
    unsimplified
    $ AndF And {andSort = predicateSort, andFirst, andSecond}

mkApplySymbol :: Symbol -> [Simplifiable variable] -> Simplifiable variable
mkApplySymbol symbol children =
    unsimplified
    $ ApplySymbolF Application
        {applicationSymbolOrAlias = symbol, applicationChildren = children}

mkApplyAlias
    :: Alias (TermLike Variable)
    -> [Simplifiable variable]
    -> Simplifiable variable
mkApplyAlias alias children =
    unsimplified
    $ ApplyAliasF Application
        {applicationSymbolOrAlias = alias, applicationChildren = children}

mkBottom :: Simplifiable variable
mkBottom =  unsimplified mkBottomF

mkBottomF :: TermLikeF variable (Simplifiable variable)
mkBottomF =  BottomF Bottom {bottomSort = predicateSort}

mkCeil :: Simplifiable variable -> Simplifiable variable
mkCeil ceilChild =
    unsimplified
    $ CeilF Ceil
        { ceilOperandSort = predicateSort
        , ceilResultSort = predicateSort
        , ceilChild
        }

mkDomainValue
    :: DomainValue Sort (Simplifiable variable) -> Simplifiable variable
mkDomainValue = unsimplified . DomainValueF

mkEquals
    :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkEquals equalsFirst equalsSecond =
    unsimplified
    $ EqualsF Equals
        { equalsOperandSort = predicateSort
        , equalsResultSort = predicateSort
        , equalsFirst
        , equalsSecond
        }

mkExists
    :: ElementVariable variable
    -> Simplifiable variable
    -> Simplifiable variable
mkExists existsVariable existsChild =
    unsimplified
    $ ExistsF Exists { existsSort = predicateSort, existsVariable, existsChild }

mkFloor :: Simplifiable variable -> Simplifiable variable
mkFloor floorChild =
    unsimplified
    $ FloorF Floor
        { floorOperandSort = predicateSort
        , floorResultSort = predicateSort
        , floorChild
        }

mkForall
    :: ElementVariable variable
    -> Simplifiable variable
    -> Simplifiable variable
mkForall forallVariable forallChild =
    unsimplified
    $ ForallF Forall { forallSort = predicateSort, forallVariable, forallChild }

mkIff :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkIff iffFirst iffSecond =
    unsimplified
    $ IffF Iff {iffSort = predicateSort, iffFirst, iffSecond}

mkImplies
    :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkImplies impliesFirst impliesSecond =
    unsimplified
    $ ImpliesF Implies
        {impliesSort = predicateSort, impliesFirst, impliesSecond}

mkIn :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkIn inContainedChild inContainingChild =
    unsimplified
    $ InF In
        { inOperandSort = predicateSort
        , inResultSort = predicateSort
        , inContainedChild
        , inContainingChild
        }

mkMu :: SetVariable variable -> Simplifiable variable -> Simplifiable variable
mkMu muVariable muChild =
    unsimplified
    $ MuF Mu { muVariable, muChild }

mkNext :: Simplifiable variable -> Simplifiable variable
mkNext nextChild =
    unsimplified
    $ NextF Next {nextSort = predicateSort, nextChild}

mkNot :: Simplifiable variable -> Simplifiable variable
mkNot notChild =
    unsimplified
    $ NotF Not {notSort = predicateSort, notChild}

mkNu :: SetVariable variable -> Simplifiable variable -> Simplifiable variable
mkNu nuVariable nuChild =
    unsimplified
    $ NuF Nu { nuVariable, nuChild }

mkOr :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkOr orFirst orSecond =
    unsimplified (mkOrF orFirst orSecond)

mkOrF
    :: Simplifiable variable
    -> Simplifiable variable
    -> TermLikeF variable (Simplifiable variable)
mkOrF orFirst orSecond =
     OrF Or {orSort = predicateSort, orFirst, orSecond}

mkRewrites
    :: Simplifiable variable -> Simplifiable variable -> Simplifiable variable
mkRewrites rewritesFirst rewritesSecond =
    unsimplified
    $ RewritesF Rewrites
        {rewritesSort = predicateSort, rewritesFirst, rewritesSecond}

mkTop :: Simplifiable variable
mkTop = unsimplified $ TopF Top {topSort = predicateSort}

mkInhabitant :: Sort -> Simplifiable variable
mkInhabitant = unsimplified . InhabitantF . Inhabitant

mkBuiltin
    :: Domain.Builtin (TermLike Concrete) (Simplifiable variable)
    -> Simplifiable variable
mkBuiltin = unsimplified . BuiltinF

mkBuiltinList
    :: Domain.InternalList (Simplifiable variable) -> Simplifiable variable
mkBuiltinList = unsimplified . BuiltinF . Domain.BuiltinList

mkBuiltinMap
    :: Domain.InternalMap (TermLike Concrete) (Simplifiable variable)
    -> Simplifiable variable
mkBuiltinMap = unsimplified . BuiltinF . Domain.BuiltinMap

mkBuiltinSet
    :: Domain.InternalSet (TermLike Concrete) (Simplifiable variable)
    -> Simplifiable variable
mkBuiltinSet = unsimplified . BuiltinF . Domain.BuiltinSet

mkEvaluated :: Simplifiable variable -> Simplifiable variable
mkEvaluated = unsimplified . EvaluatedF . Evaluated

mkStringLiteral :: Text -> Simplifiable variable
mkStringLiteral = unsimplified . StringLiteralF . Const . StringLiteral

mkInternalBytes :: Sort -> ByteString -> Simplifiable variable
mkInternalBytes sort value =
    unsimplified
    $ InternalBytesF . Const
    $ InternalBytes
        { bytesSort = sort
        , bytesValue = value
        }

mkVar :: UnifiedVariable variable -> Simplifiable variable
mkVar = unsimplified . VariableF . Const

mkElemVar :: ElementVariable variable -> Simplifiable variable
mkElemVar = mkVar . ElemVar

{- | Construct a set variable pattern.
 -}
mkSetVar :: SetVariable variable -> Simplifiable variable
mkSetVar = mkVar . SetVar

substitute
    ::  Substitute.SubstitutionVariable variable
    =>  (UnifiedVariable variable, TermLike variable)
    ->  Simplifiable variable
    ->  Simplifiable variable
substitute substitution@(substitutedVariable, newTerm) simplifiable =
    case Recursive.project simplifiable of
        (Simplified orPatt) -> substituteOr substitution orPatt
        (PartlySimplified orPatt) -> substituteOr substitution orPatt
        (Unsimplified patt) -> case patt of
            (AndF _) -> defaultSubstitution
            (ApplySymbolF _) -> defaultSubstitution
            (ApplyAliasF _) -> defaultSubstitution
            (BottomF _) -> defaultSubstitution
            (CeilF _) -> defaultSubstitution
            (DomainValueF _) -> defaultSubstitution
            (EqualsF _) -> defaultSubstitution
            (FloorF _) -> defaultSubstitution
            (IffF _) -> defaultSubstitution
            (ImpliesF _) -> defaultSubstitution
            (InF _) -> defaultSubstitution
            (NextF _) -> defaultSubstitution
            (NotF _) -> defaultSubstitution
            (OrF _) -> defaultSubstitution
            (RewritesF _) -> defaultSubstitution
            (TopF _) -> defaultSubstitution
            (InhabitantF _) -> defaultSubstitution
            (BuiltinF _) -> defaultSubstitution
            (StringLiteralF _) -> defaultSubstitution
            (InternalBytesF _) -> defaultSubstitution
            (EndiannessF _) -> defaultSubstitution
            (SignednessF _) -> defaultSubstitution

            (VariableF (Const variable))
                | variable == substitutedVariable -> fromTermLike newTerm
                | otherwise -> defaultSubstitution

            (ExistsF Exists {existsVariable})
                | ElemVar existsVariable == substitutedVariable -> simplifiable
                | otherwise -> defaultSubstitution
            (ForallF Forall {forallVariable})
                | ElemVar forallVariable == substitutedVariable -> simplifiable
                | otherwise -> defaultSubstitution
            (MuF Mu {muVariable})
                | SetVar muVariable == substitutedVariable -> simplifiable
                | otherwise -> defaultSubstitution
            (NuF Nu {nuVariable})
                | SetVar nuVariable == substitutedVariable -> simplifiable
                | otherwise -> defaultSubstitution

            (EvaluatedF _) -> error "Unexpected unsimplified evaluated term."
          where
            defaultSubstitution =
                unsimplified (substitute substitution <$> patt)

substituteOr
    :: Substitute.SubstitutionVariable variable
    => (UnifiedVariable variable, TermLike variable)
    -> OrPattern variable
    -> Simplifiable variable
substituteOr (substitutedVariable, newTerm) orPattern =
    fromTermLike
    $ TermLike.substitute (Map.singleton substitutedVariable newTerm)
    $ OrPattern.toTermLike orPattern

freeVariables
    :: InternalVariable variable
    => Simplifiable variable
    -> Attribute.FreeVariables variable
freeVariables simplifiable =
    case Recursive.project simplifiable of
        Simplified orPattern ->
            TermLike.freeVariables (OrPattern.toTermLike orPattern)
        PartlySimplified orPattern ->
            TermLike.freeVariables (OrPattern.toTermLike orPattern)
        Unsimplified patt -> case patt of
            (AndF _) -> childVariables
            (ApplySymbolF _) -> childVariables
            (ApplyAliasF _) -> childVariables
            (BottomF _) -> childVariables
            (CeilF _) -> childVariables
            (DomainValueF _) -> childVariables
            (EqualsF _) -> childVariables
            (FloorF _) -> childVariables
            (IffF _) -> childVariables
            (ImpliesF _) -> childVariables
            (InF _) -> childVariables
            (NextF _) -> childVariables
            (NotF _) -> childVariables
            (OrF _) -> childVariables
            (RewritesF _) -> childVariables
            (TopF _) -> childVariables
            (InhabitantF _) -> childVariables
            (BuiltinF _) -> childVariables
            (StringLiteralF _) -> childVariables
            (InternalBytesF _) -> childVariables
            (EvaluatedF _) -> childVariables
            (EndiannessF _) -> childVariables
            (SignednessF _) -> childVariables

            (VariableF (Const variable)) ->
                Attribute.FreeVariables (Set.singleton variable)

            (ExistsF Exists {existsVariable}) ->
                Attribute.FreeVariables
                    (Set.delete (ElemVar existsVariable) childVariablesSet)
            (ForallF Forall {forallVariable}) ->
                Attribute.FreeVariables
                    (Set.delete (ElemVar forallVariable) childVariablesSet)
            (MuF Mu {muVariable}) ->
                Attribute.FreeVariables
                    (Set.delete (SetVar muVariable) childVariablesSet)
            (NuF Nu {nuVariable}) ->
                Attribute.FreeVariables
                    (Set.delete (SetVar nuVariable) childVariablesSet)

          where
            childVariables = Foldable.fold (freeVariables <$> patt)
            Attribute.FreeVariables childVariablesSet = childVariables
