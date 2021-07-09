{- |
Module      : Kore.Attribute.Smtlib
Description : SMT-LIB translation attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Smtlib (
    Smtlib (..),
    smtlibId,
    smtlibSymbol,
    smtlibAttribute,
    applySExpr,
    shortenSExpr,
) where

import qualified Control.Error as Error
import qualified Data.Text as Text
import Kore.Attribute.Smtlib.Smtlib
import qualified Kore.Builtin.Error as Builtin.Error
import Prelude.Kore
import SMT.SimpleSMT

shortenSExpr :: SExpr -> SExpr
shortenSExpr (List [e]) = e
shortenSExpr e = e

{- | Fill placeholder symbols in an 'SExpr' from the argument list.

A placeholder is the character @#@ followed by a decimal numeral.

If the 'SExpr' is an 'Atom' at the top level, it is taken to be the head of an
'SExpr' that takes indefinitely-many arguments.
-}
applySExpr ::
    -- | 'SExpr' containing placeholder symbols
    SExpr ->
    -- | list of arguments
    [SExpr] ->
    SExpr
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
    fillN n = fromMaybe wrongArity . (`Error.atZ` (n - 1))

    ~wrongArity = Builtin.Error.wrongArity "smtlib"
