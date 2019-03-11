{-|
Module      : Kore.Attribute.Smtlib
Description : SMT-LIB translation attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Smtlib
    ( Smtlib (..)
    , smtlibId, smtlibSymbol, smtlibAttribute
    , applySExpr
    , shortenSExpr
    ) where

import qualified Control.Error as Error
import           Data.Maybe
                 ( fromMaybe )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           SimpleSMT

import           Kore.AST.Kore
import           Kore.Attribute.Smtlib.Smtlib
import qualified Kore.Builtin.Error as Builtin.Error

-- | Kore symbol representing the @smtlib@ attribute.
smtlibSymbol :: SymbolOrAlias Object
smtlibSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = smtlibId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @smtlib@ attribute.
smtlibAttribute :: Text -> CommonKorePattern
smtlibAttribute syntax =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = smtlibSymbol
            , applicationChildren =
                [ (asCommonKorePattern . StringLiteralPattern)
                    (StringLiteral syntax)
                ]
            }

shortenSExpr :: SExpr -> SExpr
shortenSExpr (List [e]) = e
shortenSExpr e = e

{- | Fill placeholder symbols in an 'SExpr' from the argument list.

A placeholder is the character @#@ followed by a decimal numeral.

If the 'SExpr' is an 'Atom' at the top level, it is taken to be the head of an
'SExpr' that takes indefinitely-many arguments.

 -}
applySExpr
    :: SExpr  -- ^ 'SExpr' containing placeholder symbols
    -> [SExpr]  -- ^ list of arguments
    -> SExpr
applySExpr =
    \case
        Atom symb -> \args -> List (fillAtom symb args : args)
        list@(List _) -> fillPlacesWorker list
  where
    fillPlacesWorker =
        \case
            List sExprs -> List <$> traverse fillPlacesWorker sExprs
            Atom symb -> fillAtom symb

    fillAtom symb = fromMaybe (\_ -> Atom symb) (fillPlace symb)

    -- Fill one placeholder
    fillPlace (Text.unpack -> ('#' : num)) = do
        (n :: Int, remainder) <- Error.headMay (reads num)
        -- A placeholder is a symbol: # followed by a decimal numeral.
        -- Abort if any characters remain after parsing the numeral.
        Error.assertMay (null remainder)
        return (fillN n)
    fillPlace _ = Nothing

    -- Look up the n-th argument.
    fillN :: Int -> [SExpr] -> SExpr
    fillN n = fromMaybe wrongArity . (\args -> Error.atZ args n)

    wrongArity = Builtin.Error.wrongArity "smtlib"
