{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Equation
    ( Equation (..)
    , mkEquation
    , mapVariables
    , refreshVariables
    , isSimplificationRule
    , equationPriority
    , substitute
    , identifiers
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
    ( Symbol (..)
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , Id (..)
    , InternalVariable
    , SetVariable
    , Sort
    , TermLike
    , Variable
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Step
    ( Renaming
    )
import Kore.Syntax.Application
    ( Application (..)
    )
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Variables.Fresh as Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

data Equation variable = Equation
    { requires :: !(Predicate variable)
    , left  :: !(TermLike variable)
    , right :: !(TermLike variable)
    , ensures :: !(Predicate variable)
    , attributes :: !(Attribute.Axiom Symbol variable)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

-- | Creates a basic, unconstrained, Equality pattern
mkEquation
    :: HasCallStack
    => InternalVariable variable
    => Sort
    -> TermLike variable
    -> TermLike variable
    -> Equation variable
mkEquation sort left right =
    assert (TermLike.termLikeSort left == TermLike.termLikeSort right)
    Equation
        { left
        , requires = Predicate.makeTruePredicate sort
        , right
        , ensures = Predicate.makeTruePredicate sort
        , attributes = Default.def
        }

instance NFData variable => NFData (Equation variable)

instance SOP.Generic (Equation variable)

instance SOP.HasDatatypeInfo (Equation variable)

instance Debug variable => Debug (Equation variable)

instance (Debug variable, Diff variable) => Diff (Equation variable)

instance InternalVariable variable => Pretty (Equation variable) where
    pretty equation@(Equation _ _ _ _ _) =
        Pretty.vsep
            [ "requires:"
            , Pretty.indent 4 (unparse requires)
            , "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (unparse ensures)
            ]
      where
        Equation
            { requires
            , left
            , right
            , ensures
            } = equation

instance TopBottom (Equation variable) where
    isTop _ = False
    isBottom _ = False

instance SQL.Table (Equation Variable)

instance SQL.Column (Equation Variable) where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

instance
    InternalVariable variable
    => From (Equation variable) (TermLike variable)
  where
    from equation
      -- \ceil axiom
      | isTop requires
      , isTop ensures
      , TermLike.Ceil_ _ sort1 _ <- left
      , TermLike.Top_ sort2 <- right
      , sort1 == sort2
      = left

      -- unconditional equation
      | isTop requires
      , isTop ensures
      = TermLike.mkEquals sort left right

      -- conditional equation
      | otherwise =
        TermLike.mkImplies
            requires'
            (TermLike.mkAnd
                (TermLike.mkEquals sort left right)
                ensures'
            )
      where
        requires' = from @(Predicate variable) requires
        ensures' = from @(Predicate variable) ensures
        sort = termLikeSort requires'
        Equation { left, requires, right, ensures } = equation

instance
    InternalVariable variable
    => HasFreeVariables (Equation variable) variable
  where
    freeVariables rule@(Equation _ _ _ _ _) = case rule of
        Equation { left, requires, right, ensures } ->
            freeVariables left
            <> freeVariables requires
            <> freeVariables right
            <> freeVariables ensures

mapVariables
    :: (Ord variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> Equation variable1 -> Equation variable2
mapVariables mapElemVar mapSetVar equation@(Equation _ _ _ _ _) =
    equation
        { requires = mapPredicateVariables requires
        , left = mapTermLikeVariables left
        , right = mapTermLikeVariables right
        , ensures = mapPredicateVariables ensures
        , attributes =
            Attribute.mapAxiomVariables mapElemVar mapSetVar attributes
        }
  where
    Equation { requires, left, right, ensures, attributes } = equation
    mapTermLikeVariables = TermLike.mapVariables mapElemVar mapSetVar
    mapPredicateVariables = Predicate.mapVariables mapElemVar mapSetVar

refreshVariables
    :: InternalVariable variable
    => FreeVariables variable
    -> Equation variable
    -> (Renaming variable, Equation variable)
refreshVariables
    (FreeVariables.getFreeVariables -> avoid)
    equation@(Equation _ _ _ _ _)
  =
    let rename = Fresh.refreshVariables avoid originalFreeVariables
        mapElemVars elemVar =
            case Map.lookup (ElemVar elemVar) rename of
                Just (ElemVar elemVar') -> elemVar'
                _ -> elemVar
        mapSetVars setVar =
            case Map.lookup (SetVar setVar) rename of
                Just (SetVar setVar') -> setVar'
                _ -> setVar
        subst = TermLike.mkVar <$> rename
        left' = TermLike.substitute subst left
        requires' = Predicate.substitute subst requires
        right' = TermLike.substitute subst right
        ensures' = Predicate.substitute subst ensures
        attributes' =
            Attribute.mapAxiomVariables mapElemVars mapSetVars attributes
        equation' =
            equation
                { left = left'
                , requires = requires'
                , right = right'
                , ensures = ensures'
                , attributes = attributes'
                }
    in (rename, equation')
  where
    Equation { left, requires, right, ensures, attributes } = equation
    originalFreeVariables =
        FreeVariables.getFreeVariables $ freeVariables equation

isSimplificationRule :: Equation variable -> Bool
isSimplificationRule Equation { attributes } =
    isSimplification
  where
    Attribute.Simplification { isSimplification } =
        Attribute.simplification attributes

equationPriority :: Equation variable -> Integer
equationPriority = Attribute.getPriorityOfAxiom . attributes

substitute
    :: InternalVariable variable
    => Map (UnifiedVariable variable) (TermLike variable)
    -> Equation variable
    -> Equation variable
substitute assignments equation =
    Equation
        { requires = Predicate.substitute assignments requires
        , left = TermLike.substitute assignments left
        , right = TermLike.substitute assignments right
        , ensures = Predicate.substitute assignments ensures
        , attributes
        }
  where
    Equation { requires, left, right, ensures, attributes } = equation

{- | The list of identifiers for an 'Equation'.

The identifiers are:

* the rule label
* symbol names on the left-hand side
* symbol 'Klabel's on the left-hand side

 -}
identifiers :: Equation variable -> [Text]
identifiers Equation { left, attributes } =
    rule <> symbols
  where
    symbols =
        flip Recursive.fold left $ \case
            _ :< TermLike.ApplySymbolF application ->
                applySymbolIdentifiers application <> Foldable.fold application
            termLikeF -> Foldable.fold termLikeF
    rule = maybe [] pure $ Attribute.unLabel $ Attribute.label attributes

    applySymbolIdentifiers application =
        catMaybes [symbolName, symbolKlabel]
      where
        Application { applicationSymbolOrAlias = symbol } = application
        symbolName = Just . getId $ symbolConstructor symbol
        symbolKlabel =
            (Attribute.Symbol.getKlabel . Attribute.Symbol.klabel)
            (symbolAttributes symbol)
