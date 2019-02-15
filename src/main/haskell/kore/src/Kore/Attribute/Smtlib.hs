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

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Error as Error
import qualified Control.Monad as Monad
import           Data.Default
import           Data.Maybe
                 ( fromMaybe, isNothing )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )
import           SimpleSMT

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..), Parser )
import qualified Kore.Attribute.Parser as Parser
import qualified Kore.Builtin.Error as Builtin.Error
import qualified Kore.Error

{- | The @smtlib@ attribute for symbols.

The @smtlib@ attribute allows a Kore symbol and its arguments to be translated
for an external SMT solver.

Kore syntax: @smtlib{}(\"≪S-expression≫\")@, where @≪S-expression≫@ is an
S-expression defined by the SMT-LIB 2 standard. If @≪S-expression≫@ is an atom,
that atom is used as the head of a list expression and all the arguments of the
hooked Kore symbol are passed as arguments of the list. If @≪S-expression≫@ is a
list, that list is passed to the SMT solver; in this case, the special
meta-variable symbols @#≪n≫@ (where @≪n≫@ is a positive integer) are replaced by
the positional parameters of the hooked Kore symbol. Note that the
meta-variable symbols are only valid in the @smtlib@ attribute; they are /not/
valid SMT-LIB S-expressions.

 -}
newtype Smtlib = Smtlib { getSmtlib :: Maybe SExpr }
    deriving (Generic, Eq, Ord, Show)

instance Default Smtlib where
    def = Smtlib Nothing

instance ParseAttributes Smtlib where
    parseAttribute =
        withApplication $ \params args Smtlib { getSmtlib } -> do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            StringLiteral syntax <- Parser.getStringLiteral arg
            sExpr <- parseSExpr syntax
            Monad.unless (isNothing getSmtlib) failDuplicate
            return Smtlib { getSmtlib = Just sExpr }
      where
        withApplication = Parser.withApplication smtlibId
        failDuplicate = Parser.failDuplicate smtlibId

instance NFData Smtlib

-- | Kore identifier representing the @smtlib@ attribute symbol.
smtlibId :: Id Object
smtlibId = "smtlib"

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

{- | Parse an 'SExpr' for the @smtlib@ attribute.

An error is signalled in 'Parser' if we cannot parse the 'SExpr', or if the
entire argument is not consumed by the parser.

 -}
parseSExpr
    :: Text  -- ^ text representing an 'SExpr'
    -> Parser SExpr
parseSExpr syntax =
    case readSExprs syntax of
        [] -> noParse
        sExpr : rest ->
            case rest of
                [] -> return sExpr
                _ -> incompleteParse
  where
    noParse = Kore.Error.koreFail "failed to parse S-expression"
    incompleteParse =
        Kore.Error.koreFail "failed to parse entire argument"

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
