{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Builtin functions. Only a select few functions are implemented.

Built-in functions are looked up by their symbol attribute 'hook' from
the definition's symbol map.
-}
module Booster.Builtin (
    hooks,
) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Prettyprinter (pretty, vsep)

import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Util
import Booster.Prettyprinter

-- built-in functions may fail on arity or sort errors, and may be
-- partial (returning a Maybe type)
type BuiltinFunction = [Term] -> Except Text (Maybe Term)

hooks :: Map Text BuiltinFunction
hooks =
    Map.unions
        [ builtinsKEQUAL
        ]

------------------------------------------------------------
(~~>) :: Text -> BuiltinFunction -> (Text, BuiltinFunction)
(~~>) = (,)

------------------------------------------------------------
-- KEQUAL hooks
builtinsKEQUAL :: Map Text BuiltinFunction
builtinsKEQUAL =
    Map.fromList
        [ "KEQUAL.ite" ~~> iteHook
        ]

iteHook :: BuiltinFunction
iteHook args
    | [cond, thenVal, elseVal] <- args = do
        cond `shouldHaveSort` "SortBool"
        unless (sortOfTerm thenVal == sortOfTerm elseVal) $
            throwE . renderText . vsep $
                [ "Different sorts in alternatives:"
                , pretty thenVal
                , pretty elseVal
                ]
        case cond of
            TrueBool -> pure $ Just thenVal
            FalseBool -> pure $ Just elseVal
            _other -> pure Nothing
    | otherwise =
        throwE . renderText $ "KEQUAL.ite: wrong arity " <> pretty (length args)

-- check for simple (parameter-less) sorts
shouldHaveSort :: Term -> SortName -> Except Text ()
t `shouldHaveSort` s
    | sortOfTerm t == SortApp s [] =
        pure ()
    | otherwise =
        throwE . renderText . vsep $
            [ pretty $ "Argument term has unexpected sort (expected " <> show s <> "):"
            , pretty t
            ]
