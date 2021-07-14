{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Equation.Validate (
    validateAxiom,
) where

import Control.Monad.State.Strict (
    StateT,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Text (
    pack,
 )
import Kore.AST.Error
import Kore.Attribute.Axiom (
    Assoc (..),
    Comm (..),
    Idem (..),
    Overload (..),
    Unit (..),
 )
import qualified Kore.Attribute.Axiom as Attribute (
    Axiom (..),
 )
import qualified Kore.Builtin.List.List as List
import qualified Kore.Builtin.Map.Map as Map
import qualified Kore.Builtin.Set.Set as Set
import Kore.Equation.Equation (
    Equation (..),
    isSimplificationRule,
 )
import Kore.Equation.Sentence (
    MatchEquationError (..),
    fromSentenceAxiom,
 )
import Kore.Internal.Predicate (
    pattern PredicateCeil,
    pattern PredicateIn,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Symbol
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Definition
import Kore.Syntax.Variable
import Kore.Unparser (
    unparse,
 )
import Kore.Validate.Verifier
import qualified Kore.Verified as Verified
import Prelude.Kore
import qualified Pretty

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
                $ asum $ getNotVar <$> termLikeF

        getNotVar (TermLike.Var_ _) = Nothing
        getNotVar term = Just term

    checkArg _ Nothing = return ()
    checkArg eq (Just arg) =
        traverse_
            ( failOnJust eq "Found invalid subterm in argument of function equation:"
                . checkArgIn
            )
            $ Predicate.getMultiAndPredicate arg
      where
        checkArgIn (PredicateIn (TermLike.Var_ _) term) =
            findBadArgSubterm term
        checkArgIn (PredicateCeil (TermLike.And_ _ (TermLike.Var_ _) term)) =
            findBadArgSubterm term
        checkArgIn badArg = Just $ Predicate.fromPredicate_ badArg

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
    failOnJust eq errorMessage (Just term) =
        koreFailWithLocations
            [term]
            ( pack $
                show $
                    Pretty.vsep
                        [ errorMessage
                        , Pretty.indent 4 $ unparse term
                        , "The equation that the above occurs in is:"
                        , Pretty.indent 4 $ Pretty.pretty eq
                        ]
            )
