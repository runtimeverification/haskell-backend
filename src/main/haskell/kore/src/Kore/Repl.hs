{-|
Module      : Kore.Repl
Description : Logging functions.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl
    ( runRepl
    ) where

import           Control.Monad.Extra
                 ( loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( StateT )
import           Control.Monad.State.Strict
                 ( evalStateT, get )
import           Data.Functor
                 ( ($>) )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Text
                 ( Text )
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( Parsec, many, parseMaybe, (<|>) )
import           Text.Megaparsec.Char
import           Text.Megaparsec.Char.Lexer
                 ( decimal )

import           Control.Error
                 ( atZ )
import           Data.List
                 ( intersperse )
import qualified Kore.AST.Common as Kore
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.OnePath.Verification
                 ( Axiom (..) )
import           Kore.OnePath.Verification
                 ( Claim (..) )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
                 ( unparseToString )
import           Kore.Unparser
                 ( Unparse )

runRepl
    :: MetadataTools Object StepperAttributes
    -> StepPatternSimplifier Object Kore.Variable
    -> PredicateSubstitutionSimplifier Object Simplifier
    -> [Axiom Object]
    -> [Claim Object]
    -> Simplifier ()
runRepl tools simplifier predicateSimplifier axioms claims
  = do
    replGreeting
    command <- maybe ShowUsage id . parseMaybe commandParser <$> prompt
    evalStateT (loopM repl0 command) state
  where
    state :: ReplState
    state =
        ReplState
            $ Map.fromList
                [ ("axioms", List $ unAxiom <$> axioms)
                , ("claims", List $ unClaim <$> claims)
                ]

    unAxiom :: Axiom Object -> RewriteRule Object Kore.Variable
    unAxiom (Axiom rule) = rule

    unClaim :: Claim Object -> RewriteRule Object Kore.Variable
    unClaim Claim { rule } = rule

    repl0 :: ReplCommand -> StateT ReplState Simplifier (Either ReplCommand ())
    repl0 cmd = do
        continue <- replInterpreter cmd
        if continue
            then
                maybe
                    (Left ShowUsage)
                    Left
                    . parseMaybe commandParser <$> prompt
            else pure . pure $ ()

data Variable
    = forall a. Unparse a => Variable a
    | forall a. Unparse a => List [a]

data ReplState = ReplState
    { variables :: Map String Variable
    }

data ReplCommand
    = ShowUsage
    | Help
    | ShowVariables
    | ShowVariable !String
    | ShowArrayItem !String !Int
    | Exit

type Parser = Parsec String String

commandParser :: Parser ReplCommand
commandParser =
    help0
    <|> showVariables0
    <|> showArrayItem0
    <|> exit0
  where
    help0 :: Parser ReplCommand
    help0 = string "help" $> Help

    showVariables0 :: Parser ReplCommand
    showVariables0 = string "showVars" $> ShowVariables

    showArrayItem0 :: Parser ReplCommand
    showArrayItem0 =
        ShowArrayItem
        <$> (string "showArray" *> space *> many letterChar)
        <*> (space1 *> decimal)

    exit0 :: Parser ReplCommand
    exit0 = string "exit" $> Exit

replInterpreter :: ReplCommand -> StateT ReplState Simplifier Bool
replInterpreter =
    \case
        ShowUsage -> showUsage0 $> True
        Help -> help0 $> True
        ShowVariables -> showVariables0 $> True
        ShowArrayItem k i -> showArrayItem0 k i $> True
        Exit -> pure False
        _ -> pure True
  where
    showUsage0 :: StateT st Simplifier ()
    showUsage0 = liftIO $ do
        putStrLn "usage!"

    help0 :: StateT st Simplifier ()
    help0 = liftIO $ do
        putStrLn "help!"

    showVariables0 :: StateT ReplState Simplifier ()
    showVariables0 = do
        vars <- Map.keys . variables <$> get
        liftIO . putStrLn . concat . intersperse " " $ vars

    showArrayItem0 :: String -> Int -> StateT ReplState Simplifier ()
    showArrayItem0 key index = do
        var <- Map.lookup key . variables <$> get
        liftIO . putStrLn . maybe "Not found" unparse'
            $ var >>= toVariable index

    toVariable :: Int -> Variable -> Maybe Variable
    toVariable index (List l) = Variable  <$> atZ l index
    toVariable _ _ = Nothing

    unparse' :: Variable -> String
    unparse' (Variable v) = unparseToString v
    unparse' _ = ""

replGreeting :: MonadIO m => m ()
replGreeting =
    liftIO $ putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

prompt :: MonadIO m => m String
prompt = liftIO $ do
    putStr "Kore> "
    hFlush stdout
    getLine

showHelp :: IO ()
showHelp =
    putStrLn
        "Commands available from the prompt: \n\
        \help                shows this help message\n\
        \proof               shows the current proof\n\
        \go                  starts the automated prover"

showError :: IO ()
showError = putStrLn "\nUnknown command. Try 'help'."
