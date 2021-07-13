{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Equation.Equation (
    Equation (..),
    mkEquation,
    toTermLike,
    toTermLikeOld,
    mapVariables,
    refreshVariables,
    isSimplificationRule,
    equationPriority,
    identifiers,
) where

import qualified Control.Lens as Lens
import qualified Data.Default as Default
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Wrapped (
    _Wrapped,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import Debug
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.AST.AstWithLocation
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    HasFreeVariables (..),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Internal.Predicate (
    Predicate,
    fromPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol (
    Symbol (..),
 )
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    mkVar,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.Step (
    Renaming,
 )
import Kore.Sort
import Kore.Substitute
import Kore.Syntax.Application (
    Application (..),
 )
import Kore.Syntax.Variable
import Kore.TopBottom
import Kore.Unparser (
    Unparse (..),
 )
import qualified Kore.Variables.Fresh as Fresh
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty
import qualified SQL

data Equation variable = Equation
    { requires :: !(Predicate variable)
    , argument :: !(Maybe (Predicate variable))
    , antiLeft :: !(Maybe (Predicate variable))
    , left :: !(TermLike variable)
    , right :: !(TermLike variable)
    , ensures :: !(Predicate variable)
    , attributes :: !(Attribute.Axiom Symbol variable)
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

-- | Creates a basic, unconstrained, Equality pattern
mkEquation ::
    HasCallStack =>
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    Equation variable
mkEquation left right =
    assert
        (TermLike.termLikeSort left == TermLike.termLikeSort right)
        Equation
            { left
            , requires = Predicate.makeTruePredicate
            , argument = Nothing
            , antiLeft = Nothing
            , right
            , ensures = Predicate.makeTruePredicate
            , attributes = Default.def
            }

instance InternalVariable variable => Pretty (Equation variable) where
    pretty equation@(Equation _ _ _ _ _ _ _) =
        Pretty.vsep
            [ "requires:"
            , Pretty.indent 4 (pretty requires)
            , "argument:"
            , Pretty.indent 4 (maybe "" pretty argument)
            , "antiLeft:"
            , Pretty.indent 4 (maybe "" pretty antiLeft)
            , "left:"
            , Pretty.indent 4 (unparse left)
            , "right:"
            , Pretty.indent 4 (unparse right)
            , "ensures:"
            , Pretty.indent 4 (pretty ensures)
            ]
      where
        Equation
            { requires
            , argument
            , antiLeft
            , left
            , right
            , ensures
            } = equation

instance TopBottom (Equation variable) where
    isTop _ = False
    isBottom _ = False

instance SQL.Table (Equation VariableName)

instance SQL.Column (Equation VariableName) where
    defineColumn = SQL.defineForeignKeyColumn
    toColumn = SQL.toForeignKeyColumn

instance InternalVariable variable => Substitute (Equation variable) where
    type TermType (Equation variable) = TermLike variable

    type VariableNameType (Equation variable) = variable

    substitute assignments equation =
        Equation
            { requires = substitute assignments (requires equation)
            , argument = substitute assignments <$> argument equation
            , antiLeft = substitute assignments <$> antiLeft equation
            , left = substitute assignments (left equation)
            , right = substitute assignments (right equation)
            , ensures = substitute assignments (ensures equation)
            , attributes = attributes equation
            }

    rename = substitute . fmap mkVar
    {-# INLINE rename #-}

-- This function must be removed as part of https://github.com/kframework/kore/issues/2593
toTermLikeOld ::
    InternalVariable variable =>
    Sort ->
    Equation variable ->
    TermLike variable
toTermLikeOld sort equation
    -- \ceil axiom
    | isTop requires
      , isTop ensures
      , TermLike.Ceil_ _ sort1 _ <- left
      , TermLike.Top_ sort2 <- right
      , sort1 == sort2 =
        left
    -- function rule
    | Just argument' <- argument
      , Just antiLeft' <- antiLeft =
        let antiLeftTerm = fromPredicate sort antiLeft'
            argumentTerm = fromPredicate sort argument'
         in TermLike.mkImplies
                ( TermLike.mkAnd
                    antiLeftTerm
                    ( TermLike.mkAnd
                        requires'
                        argumentTerm
                    )
                )
                ( TermLike.mkAnd
                    (TermLike.mkEquals sort left right)
                    ensures'
                )
    -- function rule without priority
    | Just argument' <- argument =
        let argumentTerm = fromPredicate sort argument'
         in TermLike.mkImplies
                ( TermLike.mkAnd
                    requires'
                    (TermLike.mkAnd argumentTerm $ TermLike.mkTop sort)
                )
                ( TermLike.mkAnd
                    (TermLike.mkEquals sort left right)
                    ensures'
                )
    -- unconditional equation
    | isTop requires
      , isTop ensures =
        TermLike.mkEquals sort left right
    -- conditional equation
    | otherwise =
        TermLike.mkImplies
            requires'
            ( TermLike.mkAnd
                (TermLike.mkEquals sort left right)
                ensures'
            )
  where
    requires' = fromPredicate sort requires
    ensures' = fromPredicate sort ensures
    Equation
        { requires
        , argument
        , antiLeft
        , left
        , right
        , ensures
        } = equation

toTermLike ::
    InternalVariable variable =>
    Sort ->
    Equation variable ->
    TermLike variable
toTermLike sort equation
    -- \ceil axiom
    | isTop requires
      , isTop ensures
      , TermLike.Ceil_ _ sort1 _ <- left
      , TermLike.Top_ sort2 <- right
      , sort1 == sort2 =
        left
    -- function rule
    | Just argument' <- argument
      , Just antiLeft' <- antiLeft =
        let antiLeftTerm = fromPredicate sort antiLeft'
            argumentTerm = fromPredicate sort argument'
         in TermLike.mkImplies
                ( TermLike.mkAnd
                    antiLeftTerm
                    ( TermLike.mkAnd
                        requires'
                        argumentTerm
                    )
                )
                ( TermLike.mkEquals sort left $
                    TermLike.mkAnd right ensures'
                )
    -- function rule without priority
    | Just argument' <- argument =
        let argumentTerm = fromPredicate sort argument'
         in TermLike.mkImplies
                ( TermLike.mkAnd
                    requires'
                    (TermLike.mkAnd argumentTerm $ TermLike.mkTop sort)
                )
                ( TermLike.mkEquals sort left $
                    TermLike.mkAnd right ensures'
                )
    -- unconditional equation
    | isTop requires
      , isTop ensures =
        TermLike.mkEquals sort left right
    -- conditional equation
    | otherwise =
        TermLike.mkImplies
            requires'
            ( TermLike.mkEquals sort left $
                TermLike.mkAnd right ensures'
            )
  where
    requires' = fromPredicate sort requires
    ensures' = fromPredicate rightSort ensures
    Equation
        { requires
        , argument
        , antiLeft
        , left
        , right
        , ensures
        } = equation
    rightSort = TermLike.termLikeSort right

instance
    InternalVariable variable =>
    HasFreeVariables (Equation variable) variable
    where
    freeVariables rule@(Equation _ _ _ _ _ _ _) = case rule of
        Equation{left, argument, antiLeft, requires, right, ensures} ->
            freeVariables left
                <> freeVariables requires
                <> maybe mempty freeVariables argument
                <> maybe mempty freeVariables antiLeft
                <> freeVariables right
                <> freeVariables ensures

instance AstWithLocation variable => AstWithLocation (Equation variable) where
    locationFromAst = locationFromAst . left

mapVariables ::
    (InternalVariable variable1, InternalVariable variable2) =>
    AdjSomeVariableName (variable1 -> variable2) ->
    Equation variable1 ->
    Equation variable2
mapVariables mapping equation@(Equation _ _ _ _ _ _ _) =
    equation
        { requires = mapPredicateVariables requires
        , argument = mapPredicateVariables <$> argument
        , antiLeft = mapPredicateVariables <$> antiLeft
        , left = mapTermLikeVariables left
        , right = mapTermLikeVariables right
        , ensures = mapPredicateVariables ensures
        , attributes = Attribute.mapAxiomVariables mapping attributes
        }
  where
    Equation
        { requires
        , argument
        , antiLeft
        , left
        , right
        , ensures
        , attributes
        } = equation
    mapTermLikeVariables = TermLike.mapVariables mapping
    mapPredicateVariables = Predicate.mapVariables mapping

refreshVariables ::
    forall variable.
    InternalVariable variable =>
    FreeVariables variable ->
    Equation variable ->
    (Renaming variable, Equation variable)
refreshVariables
    (FreeVariables.toNames -> avoid)
    equation@(Equation _ _ _ _ _ _ _) =
        let rename' :: Map (SomeVariableName variable) (SomeVariable variable)
            rename' =
                FreeVariables.toSet originalFreeVariables
                    & Fresh.refreshVariables avoid
            lookupSomeVariableName ::
                forall variable'.
                Injection (SomeVariableName variable) variable' =>
                variable' ->
                variable'
            lookupSomeVariableName variable =
                do
                    let injected = inject @(SomeVariableName _) variable
                    someVariableName <- variableName <$> Map.lookup injected rename'
                    retract someVariableName
                    & fromMaybe variable
            adj :: AdjSomeVariableName (variable -> variable)
            adj =
                AdjSomeVariableName
                    { adjSomeVariableNameElement =
                        ElementVariableName . Lens.over _Wrapped $
                            lookupSomeVariableName @(ElementVariableName _)
                    , adjSomeVariableNameSet =
                        SetVariableName . Lens.over _Wrapped $
                            lookupSomeVariableName @(SetVariableName _)
                    }
            subst :: Map (SomeVariableName variable) (TermLike variable)
            subst =
                FreeVariables.toList originalFreeVariables
                    & map mkSubst
                    & Map.fromList
            mkSubst variable =
                ( variableName variable
                , TermLike.mkVar (mapSomeVariable adj variable)
                )
            left' = substitute subst left
            requires' = substitute subst requires
            argument' = substitute subst <$> argument
            antiLeft' = substitute subst <$> antiLeft
            right' = substitute subst right
            ensures' = substitute subst ensures
            attributes' = Attribute.mapAxiomVariables adj attributes
            equation' =
                equation
                    { left = left'
                    , requires = requires'
                    , argument = argument'
                    , antiLeft = antiLeft'
                    , right = right'
                    , ensures = ensures'
                    , attributes = attributes'
                    }
         in (rename', equation')
      where
        Equation
            { requires
            , argument
            , antiLeft
            , left
            , right
            , ensures
            , attributes
            } = equation
        originalFreeVariables = freeVariables equation

isSimplificationRule :: Equation variable -> Bool
isSimplificationRule Equation{attributes} =
    case Attribute.simplification attributes of
        Attribute.IsSimplification _ -> True
        _ -> False

equationPriority :: Equation variable -> Integer
equationPriority = Attribute.getPriorityOfAxiom . attributes

{- | The list of identifiers for an 'Equation'.

The identifiers are:

* the rule label
* symbol names on the left-hand side
* symbol 'Klabel's on the left-hand side
-}
identifiers :: Equation variable -> [Text]
identifiers Equation{left, attributes} =
    rule <> symbols
  where
    symbols =
        flip Recursive.fold left $ \case
            _ :< TermLike.ApplySymbolF application ->
                applySymbolIdentifiers application <> fold application
            termLikeF -> fold termLikeF
    rule = maybe [] pure $ Attribute.unLabel $ Attribute.label attributes

    applySymbolIdentifiers application =
        catMaybes [symbolName, symbolKlabel]
      where
        Application{applicationSymbolOrAlias = symbol} = application
        symbolName = Just . getId $ symbolConstructor symbol
        symbolKlabel =
            (Attribute.Symbol.getKlabel . Attribute.Symbol.klabel)
                (symbolAttributes symbol)
