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
import           Data.Maybe
                 ( fromMaybe )

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
    fromMaybe (\_ -> pure ())
    (getHook hook >>= flip HashMap.lookup sortVerifiers)

{- | Look up and apply a builtin symbol verifier.

  The 'Hook' name should refer to a builtin symbol; if it is unset or the name is
  not recognized, verification succeeds.

 -}
symbolVerifier :: Verifiers -> Hook -> SymbolVerifier
symbolVerifier Verifiers { symbolVerifiers } hook =
    fromMaybe (\_ _ -> pure ())
    (getHook hook >>= flip HashMap.lookup symbolVerifiers)

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
    ("sort '" ++ sortName ++ "' declaration")
    (case sentenceSortParameters of
        [] -> pure ()
        _ -> koreFail ("expected 0 sort parameters, found "
                        ++ show (length sentenceSortParameters))
    )

{- | Verify a builtin sort application.

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
            ("sort '" ++ getId sortActualName
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
        ("symbol '" ++ symbolName ++ "' declaration")
        (do
            withContext "result sort"
                (verifySort findSort builtinResult result)
            verifySymbolArguments builtinSorts findSort decl
        )

{- | Verify the arguments of a builtin sort declaration.

  The declared argument sorts must match the builtin argument sorts. The result
  sort is not checked. (Some builtins can be hooked to symbols that return
  non-builtin sorts.)

  See also: 'verifySymbol'

 -}
verifySymbolArguments
    :: [String]  -- ^ Builtin argument sorts
    -> SymbolVerifier
verifySymbolArguments
    builtinSorts
    findSort
    SentenceSymbol
    { sentenceSymbolSorts = sorts }
  =
    withContext "argument sorts"
    (do
        koreFailWhen (arity /= builtinArity)
            ("expected " ++ show builtinArity
             ++ " arguments, found " ++ show arity)
        zipWithM_ (verifySort findSort) builtinSorts sorts
    )
  where
    builtinArity = length builtinSorts
    arity = length sorts
