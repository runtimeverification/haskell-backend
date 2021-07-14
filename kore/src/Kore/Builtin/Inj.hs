{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.Inj (
    verifiers,
) where

import qualified Data.Functor.Foldable as Recursive
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Builtin.Verifiers (
    PatternVerifierHook (..),
    Verifiers (..),
 )
import Kore.Error
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Validate.PatternVerifier.PatternVerifier (
    PatternVerifier,
 )
import Kore.Verified as Verified
import Prelude.Kore

verifiers :: Verifiers
verifiers =
    Verifiers
        { sortDeclVerifiers = mempty
        , symbolVerifiers = mempty
        , patternVerifierHook
        }
  where
    patternVerifierHook = PatternVerifierHook $ \termLike -> do
        let _ :< termLikeF = Recursive.project termLike
        case termLikeF of
            ApplySymbolF application
                | Symbol.isSortInjection symbol -> internalizeInj application
              where
                Application{applicationSymbolOrAlias = symbol} = application
            _ -> return termLike

    expectInjParams :: [Sort] -> PatternVerifier (Sort, Sort)
    expectInjParams [fromSort, toSort] = return (fromSort, toSort)
    expectInjParams _ = koreFail "Expected two sort parameters"

    expectInjChildren :: [a] -> PatternVerifier a
    expectInjChildren [child] = return child
    expectInjChildren _ = koreFail "Expected one argument"

    internalizeInj ::
        Application Symbol Verified.Pattern ->
        PatternVerifier Verified.Pattern
    internalizeInj application = do
        (injFrom, injTo) <- expectInjParams symbolParams
        injChild <- expectInjChildren applicationChildren
        let inj =
                Inj
                    { injConstructor
                    , injFrom
                    , injTo
                    , injChild
                    , injAttributes
                    }
        -- TODO (thomas.tuegel): We cannot check the ordering of the injection's
        -- sorts at this time because the subsort axioms have not been read.
        --
        -- InjSimplifier { isOrderedInj, evaluateInj } <-
        --     Reader.asks PatternVerifier.injSimplifier
        -- let unordered = not (isOrderedInj inj)
        -- koreFailWhen unordered $ show $ Pretty.vsep
        --     [ "Illegal sort injection:"
        --     , (Pretty.indent 4 . unparse) injFrom
        --     , "is not a subsort of:"
        --     , (Pretty.indent 4 . unparse) injTo
        --     ]
        -- let InjSimplifier { evaluateInj } = injSimplifier
        -- (return . evaluateInj) inj
        return (synthesize $ InjF inj)
      where
        Application{applicationSymbolOrAlias = symbol} = application
        Application{applicationChildren} = application
        Symbol{symbolConstructor = injConstructor} = symbol
        Symbol{symbolParams} = symbol
        Symbol{symbolAttributes = injAttributes} = symbol
