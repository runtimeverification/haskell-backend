{- |
Module      : Kore.Builtin.Builtin
Description : Built-in sort, symbol, and pattern verifiers
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Builtin as Builtin
@
 -}
module Kore.Builtin.Builtin
    (
      -- * Using builtin verifiers
      Verifiers (..)
    , SymbolVerifier, SymbolVerifiers
    , SortVerifier, SortVerifiers
    , PatternVerifier, PatternVerifiers
    , Function
    , symbolVerifier
    , sortVerifier
      -- * Declaring builtin verifiers
    , verifySortDecl
    , verifySort
    , verifySymbol
    , verifySymbolArguments
    , notImplemented
    ) where

import           Control.Monad
                 ( zipWithM_ )
import           Data.HashMap.Strict
                 ( HashMap )
import qualified Data.HashMap.Strict as HashMap

import Kore.AST.Common
       ( Id (..), Sort (..), SortActual (..), SortVariable (..), Symbol (..),
       Variable )
import Kore.AST.Error
       ( withLocationAndContext )
import Kore.AST.Kore
       ( CommonKorePattern )
import Kore.AST.MetaOrObject
       ( Object )
import Kore.AST.Sentence
       ( KoreSentenceSort, KoreSentenceSymbol, SentenceSort (..),
       SentenceSymbol (..) )
import Kore.ASTVerifier.Error
       ( VerifyError, VerifySuccess )
import Kore.Attribute.Parser
       ( parseAttributes )
import Kore.Builtin.Hook
       ( Hook (..) )
import Kore.Error
       ( Error, castError, koreFail, koreFailWhen, withContext )
import Kore.IndexedModule.IndexedModule
       ( SortDescription )
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (ApplicationFunctionEvaluator),
       AttemptedFunction (NotApplicable),
       FunctionResultProof (FunctionResultProof) )

type Function = ApplicationFunctionEvaluator Object Variable

type SortVerifier =
       KoreSentenceSort Object
    -- ^ Sort declaration to verify
    -> Either (Error VerifyError) ()

-- | @SortVerifiers@ associates a @SortVerifier@ with its builtin sort name.
type SortVerifiers = HashMap String SortVerifier

type SymbolVerifier =
       (Id Object -> Either (Error VerifyError) (SortDescription Object))
    -- ^ Find a sort declaration
    -> KoreSentenceSymbol Object
    -- ^ Symbol declaration to verify
    -> Either (Error VerifyError) ()

{- | @SymbolVerifiers@ associates a @SymbolVerifier@ with each builtin
  symbol name.
 -}
type SymbolVerifiers = HashMap String SymbolVerifier

type PatternVerifier =
    CommonKorePattern -> Either (Error VerifyError) VerifySuccess

type PatternVerifiers = HashMap String PatternVerifier

{- | Verify builtin sorts, symbols, and patterns.
 -}
data Verifiers =
    Verifiers
    { sortVerifiers :: SortVerifiers
    , symbolVerifiers :: SymbolVerifiers
    , patternVerifiers :: PatternVerifiers
    }

{- | Look up and apply a builtin sort verifier.

  The 'Hook' name should refer to a builtin sort; if it is unset or the name is
  not recognized, verification succeeds.

 -}
sortVerifier :: Verifiers -> Hook -> SortVerifier
sortVerifier Verifiers { sortVerifiers } hook =
    let
        hookedSortVerifier :: Maybe SortVerifier
        hookedSortVerifier = do
            -- Get the builtin sort name.
            sortName <- getHook hook
            HashMap.lookup sortName sortVerifiers
    in
        case hookedSortVerifier of
            Nothing ->
                -- There is nothing to verify because either
                -- 1. the sort is not hooked, or
                -- 2. there is no SortVerifier registered to the hooked name.
                -- In either case, there is nothing more to do.
                \_ -> pure ()
            Just verifier ->
                -- Invoke the verifier that is registered to this builtin sort.
                verifier

{- | Look up and apply a builtin symbol verifier.

  The 'Hook' name should refer to a builtin symbol; if it is unset or the name is
  not recognized, verification succeeds.

 -}
symbolVerifier :: Verifiers -> Hook -> SymbolVerifier
symbolVerifier Verifiers { symbolVerifiers } hook =
    let
        hookedSymbolVerifier :: Maybe SymbolVerifier
        hookedSymbolVerifier = do
            -- Get the builtin sort name.
            symbolName <- getHook hook
            HashMap.lookup symbolName symbolVerifiers
    in
        case hookedSymbolVerifier of
            Nothing ->
                -- There is nothing to verify because either
                -- 1. the symbol is not hooked, or
                -- 2. there is no SymbolVerifier registered to the hooked name.
                -- In either case, there is nothing more to do.
                \_ _ -> pure ()
            Just verifier ->
                -- Invoke the verifier that is registered to this builtin symbol.
                verifier

notImplemented :: Function
notImplemented =
    ApplicationFunctionEvaluator notImplemented0
  where
    notImplemented0 _ _ _ _ = pure (NotApplicable, FunctionResultProof)

{- | Verify a builtin sort declaration.

  Check that the hooked sort does not take any sort parameters.

 -}
verifySortDecl :: SortVerifier
verifySortDecl
    SentenceSort
    { sentenceSortName = sortId@Id { getId = sortName }
    , sentenceSortParameters
    }
  =
    withLocationAndContext
    sortId
    ("In sort '" ++ sortName ++ "' declaration")
    (case sentenceSortParameters of
        [] -> pure ()
        _ -> koreFail ("Expected 0 sort parameters, found "
                        ++ show (length sentenceSortParameters))
    )

{- | Verify the occurrence of a builtin sort.

  Check that the sort is hooked to the named builtin. The sort parameters are
  already checked by the verifier.

 -}
verifySort
    :: (Id Object -> Either (Error VerifyError) (SortDescription Object))
    -> String
    -> Sort Object
    -> Either (Error VerifyError) ()
verifySort findSort builtinName (SortActualSort SortActual { sortActualName }) =
    do
        SentenceSort { sentenceSortAttributes } <- findSort sortActualName
        let
            expectHook = Hook (Just builtinName)
        declHook <- castError (parseAttributes sentenceSortAttributes)
        koreFailWhen (expectHook /= declHook)
            ("Sort '" ++ getId sortActualName
             ++ "' is not hooked to builtin sort '"
             ++ builtinName ++ "'")
verifySort _ _ (SortVariableSort SortVariable { getSortVariable }) =
    koreFail ("unexpected sort variable '" ++ getId getSortVariable ++ "'")

{- | Verify a builtin symbol declaration.

  The declared sorts must match the builtin sorts.

  See also: 'verifySymbolArguments'

 -}
verifySymbol
    :: String  -- ^ Builtin result sort
    -> [String]  -- ^ Builtin argument sorts
    -> SymbolVerifier
verifySymbol
    builtinResult
    builtinSorts
    findSort
    decl@SentenceSymbol
        { sentenceSymbolSymbol =
            Symbol { symbolConstructor = symbolId@Id { getId = symbolName } }
        , sentenceSymbolResultSort = result
        }
  =
    withLocationAndContext
        symbolId
        ("In symbol '" ++ symbolName ++ "' declaration")
        (do
            withContext "In result sort"
                (verifySort findSort builtinResult result)
            verifySymbolArguments builtinSorts findSort decl
        )

{- | Verify the arguments of a builtin sort declaration.

  The declared argument sorts must match the builtin argument
  sorts. @verifySymbolArguments@ only checks the symbol's argument sorts; use
  'verifySymbol' if it is also necessary to check the symbol's result sort.

  See also: 'verifySymbol'

 -}
verifySymbolArguments
    :: [String]  -- ^ Builtin argument sorts
    -> SymbolVerifier
verifySymbolArguments
    builtinSorts
    findSort
    SentenceSymbol { sentenceSymbolSorts = sorts }
  =
    withContext "In argument sorts"
    (do
        koreFailWhen (arity /= builtinArity)
            ("Expected " ++ show builtinArity
             ++ " arguments, found " ++ show arity)
        zipWithM_ (verifySort findSort) builtinSorts sorts
    )
  where
    builtinArity = length builtinSorts
    arity = length sorts
