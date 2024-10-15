{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Pretty printer for JSON KORE terms

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad (unless)
import Control.Monad.Trans.Except
import Data.Aeson (eitherDecode)
import Data.ByteString.Lazy qualified as BS
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text.IO qualified as Text
import Prettyprinter
import System.Environment (getArgs)

import Booster.Pattern.Base (Term, Variable)
import Booster.Pattern.Pretty
import Booster.Prettyprinter (renderDefault, renderText)
import Booster.Syntax.Json (KoreJson (..))
import Booster.Syntax.Json.Internalise (
    InternalisedPredicates (..),
    PatternError (..),
    internalisePattern,
    internalisePredicates,
    pattern CheckSubsorts,
    pattern DisallowAlias,
 )
import Booster.Syntax.ParsedKore (internalise, parseKoreDefinition)

main :: IO ()
main = do
    [def, json] <- getArgs
    parsedDef <-
        either (error . renderDefault . pretty) id . parseKoreDefinition def <$> Text.readFile def
    let internalDef = either (error . renderDefault . pretty' @'[Decoded]) id $ internalise Nothing parsedDef

    fileContent <- BS.readFile json
    case eitherDecode fileContent of
        Left err -> putStrLn $ "Error: " ++ err
        Right KoreJson{term} -> do
            case runExcept $ internalisePattern DisallowAlias CheckSubsorts Nothing internalDef term of
                Right (trm, preds, ceils, subst, unsupported) -> do
                    mapM_ Text.putStrLn $
                        ["Pretty-printing pattern:", renderText $ pretty' @'[Decoded] trm]
                            <> renderThings "Bool predicates:" preds
                            <> renderThings "Ceil predicates:" ceils
                            <> ["Substitution:", showSubst subst]
                    unless (null unsupported) $ do
                        putStrLn $ "...as well as " <> show (length unsupported) <> " unsupported parts:"
                        mapM_ print unsupported
                Left (NoTermFound _) ->
                    case runExcept $ internalisePredicates DisallowAlias CheckSubsorts Nothing internalDef [term] of
                        Left es -> error (show es)
                        Right ts -> do
                            mapM_ Text.putStrLn $
                                "Pretty-printing predicates:"
                                    : renderThings "Bool predicates:" ts.boolPredicates
                                        <> renderThings "Ceil predicates:" ts.ceilPredicates
                                        <> ["Substitution:", showSubst ts.substitution]
                            unless (null ts.unsupported) $ do
                                putStrLn $ "...as well as " <> show (length ts.unsupported) <> " unsupported parts:"
                                mapM_ print ts.unsupported
                Left err -> error (show err)
  where
    showSubst :: Map Variable Term -> Text
    showSubst m =
        renderText $
            vsep
                [ pretty' @'[Decoded] v <+> "->" <+> pretty' @'[Decoded] expr
                | (v, expr) <- Map.assocs m
                ]

    renderThings :: Pretty (PrettyWithModifiers '[Decoded] a) => Text -> [a] -> [Text]
    renderThings heading [] = [heading <> " -"]
    renderThings heading things = heading : map (renderText . pretty' @'[Decoded]) things
