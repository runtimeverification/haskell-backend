{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Equation.Validate (
    validateAxiom,
) where

import Control.Monad.State.Strict (
    StateT,
 )
import Data.Functor.Foldable qualified as Recursive
import Data.Text (
    pack,
 )
import Kore.AST.AstWithLocation
import Kore.AST.Error
import Kore.Attribute.Axiom (
    Assoc (..),
    Comm (..),
    Idem (..),
    Overload (..),
    Unit (..),
 )
import Kore.Attribute.Axiom qualified as Attribute (
    Axiom (..),
 )
import Kore.Builtin.List.List qualified as List
import Kore.Builtin.Map.Map qualified as Map
import Kore.Builtin.Set.Set qualified as Set
import Kore.Equation.Equation (
    Equation (..),
    isSimplificationRule,
 )
import Kore.Equation.Sentence (
    MatchEquationError (..),
    fromSentenceAxiom,
 )
import Kore.Internal.Predicate (
    Predicate,
    pattern PredicateCeil,
    pattern PredicateIn,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.Symbol qualified as Symbol
import Kore.Internal.TermLike (
    AstLocation,
    InternalVariable,
    TermLike,
    mkSortVariable,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Syntax.Definition
import Kore.Syntax.Variable
import Kore.Unparser (
    unparse,
 )
import Kore.Validate.Verifier
import Kore.Verified qualified as Verified
import Prelude.Kore
import Pretty (Doc)
import Pretty qualified

validateAxiom ::
    Attribute.Axiom TermLike.Symbol VariableName ->
    Verified.SentenceAxiom ->
    StateT VerifiedModule' Verifier ()
validateAxiom attrs verified =
    case fromSentenceAxiom (attrs, verified) of
        Right eq@Equation{left, argument} ->
            when (needsVerification eq) $
                checkLHS eq left >> checkArg eq argument
        Left err@(RequiresError _) -> failWithBadEquation err
        Left err@(ArgumentError _) -> failWithBadEquation err
        Left err@(AntiLeftError _) -> failWithBadEquation err
        Left err@(EnsuresError _) -> failWithBadEquation err
        Left (NotEquation _) -> return ()
        Left FunctionalAxiom -> return ()
        Left ConstructorAxiom -> return ()
        Left SubsortAxiom -> return ()
  where
    failWithBadEquation =
        koreFailWithLocations [sentenceAxiomPattern verified]
            . pack
            . show
            . Pretty.pretty

    needsVerification eq@Equation{attributes} =
        not
            ( isSimplificationRule eq
                || isAssoc
                || isComm
                || isUnit
                || isIdem
                || isJust getOverload
            )
      where
        Assoc{isAssoc} = Attribute.assoc attributes
        Comm{isComm} = Attribute.comm attributes
        Unit{isUnit} = Attribute.unit attributes
        Idem{isIdem} = Attribute.idem attributes
        Overload{getOverload} = Attribute.overload attributes

    checkLHS eq termLike = do
        checkAllowedFunctionSymbol
        checkVarFunctionArguments
      where
        _ :< termLikeF = Recursive.project termLike

        checkAllowedFunctionSymbol
            | TermLike.App_ sym _ <- termLike =
                unless
                    (isAllowedFunctionSymbol sym)
                    (throwIllegalFunctionSymbol sym)
            | otherwise = return ()
          where
            isAllowedFunctionSymbol sym =
                Symbol.isFunction sym && not (Symbol.isConstructorLike sym)

        throwIllegalFunctionSymbol sym =
            koreFailWithLocations [eq] $
                pack $
                    show $
                        Pretty.vsep
                            [ "Expected function symbol, but found constructor symbol:"
                            , unparse sym
                            ]

        checkVarFunctionArguments =
            failOnJust
                eq
                "Expected variable, but found:"
                (fmap unparseWithLocation $ asum $ getNotVar <$> termLikeF)

        getNotVar (TermLike.Var_ _) = Nothing
        getNotVar term = Just term

    unparseWithLocation ::
        AstWithLocation variable =>
        InternalVariable variable =>
        TermLike variable ->
        (Doc ann, AstLocation)
    unparseWithLocation t = (unparse t, locationFromAst t)

    checkArg _ Nothing = return ()
    checkArg eq (Just arg) =
        traverse_
            ( failOnJust eq "Found invalid subterm in argument of function equation:"
                . checkArgInAndUnparse
            )
            $ Predicate.getMultiAndPredicate arg
      where
        checkArgInAndUnparse ::
            AstWithLocation variable =>
            InternalVariable variable =>
            Predicate variable ->
            Maybe (Doc ann, AstLocation)
        checkArgInAndUnparse predicate =
            checkArgIn predicate <&> unparseWithLocation
          where
            checkArgIn (PredicateIn (TermLike.Var_ _) term) =
                findBadArgSubterm term
            checkArgIn (PredicateCeil (TermLike.And_ _ (TermLike.Var_ _) term)) =
                findBadArgSubterm term
            checkArgIn badArg =
                -- use dummy sort variable for pretty printing inside failOnJust
                -- the term's AstLocation will be AstLocationNone
                Just $ Predicate.fromPredicate (mkSortVariable "_") badArg
        findBadArgSubterm term = case term of
            _
                | TermLike.isConstructorLike term -> descend
            TermLike.App_ sym _
                | isGoodSymbol sym -> descend
                | otherwise -> Just term
            TermLike.InternalBytes_ _ _ -> Nothing
            TermLike.InternalBool_ _ -> Nothing
            TermLike.InternalInt_ _ -> Nothing
            TermLike.InternalString_ _ -> Nothing
            TermLike.DV_ _ (TermLike.StringLiteral_ _) -> Nothing
            TermLike.And_ _ _ _ -> descend
            TermLike.Or_ _ _ _ -> descend
            TermLike.Var_ _ -> Nothing
            TermLike.Inj_ _ -> descend
            _ -> Just term
          where
            _ :< termF = Recursive.project term
            isGoodSymbol sym =
                or
                    [ Symbol.isConstructorLike sym
                    , Symbol.isAnywhere sym && Symbol.isInjective sym
                    , Map.isSymbolConcat sym
                    , Map.isSymbolElement sym
                    , Map.isSymbolUnit sym
                    , Set.isSymbolConcat sym
                    , Set.isSymbolElement sym
                    , Set.isSymbolUnit sym
                    , List.isSymbolConcat sym
                    , List.isSymbolElement sym
                    , List.isSymbolUnit sym
                    ]
            descend = asum $ findBadArgSubterm <$> termF

    failOnJust _ _ Nothing = return ()
    failOnJust eq errorMessage (Just (term, location)) =
        koreFailWithLocations
            [location]
            ( pack $
                show $
                    Pretty.vsep
                        [ errorMessage
                        , Pretty.indent 4 term
                        , "The equation that the above occurs in is:"
                        , Pretty.indent 4 $ Pretty.pretty eq
                        ]
            )
