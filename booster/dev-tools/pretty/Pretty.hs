{-# LANGUAGE PatternSynonyms #-}

{- | Pretty printer for JSON KORE terms

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Booster.Prettyprinter (renderDefault)
import Booster.Syntax.Json (KoreJson (..))
import Booster.Syntax.Json.Internalise (
    internalisePattern,
    pattern CheckSubsorts,
    pattern DisallowAlias,
 )
import Booster.Syntax.ParsedKore (internalise, parseKoreDefinition)
import Control.Monad.Trans.Except
import Data.Aeson (eitherDecode)
import Data.ByteString.Lazy qualified as BS
import Data.Text.IO qualified as Text
import Prettyprinter
import System.Environment (getArgs)

main :: IO ()
main = do
    [def, json] <- getArgs
    parsedDef <-
        either (error . renderDefault . pretty) id . parseKoreDefinition def <$> Text.readFile def
    let internalDef = either (error . renderDefault . pretty) id $ internalise Nothing parsedDef

    fileContent <- BS.readFile json
    case eitherDecode fileContent of
        Left err -> putStrLn $ "Error: " ++ err
        Right KoreJson{term} -> do
            let (trm, _subst, _unsupported) =
                    either (error . show) id $
                        runExcept $
                            internalisePattern DisallowAlias CheckSubsorts Nothing internalDef term
            putStrLn $ renderDefault $ pretty trm
