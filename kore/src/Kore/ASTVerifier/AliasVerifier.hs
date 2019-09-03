{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.ASTVerifier.AliasVerifier
    ( verifyAliases ) where

import qualified Control.Lens as Lens
import           Control.Monad.Reader
                 ( ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Class as State
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import           Data.Function
import qualified Data.Functor.Foldable as Recursive
import           Data.Generics.Product
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC

import           Kore.AST.Error
import           Kore.ASTVerifier.SentenceVerifier
                 ( SentenceVerifier )
import qualified Kore.ASTVerifier.SentenceVerifier as SentenceVerifier
import           Kore.Attribute.Parser
                 ( liftParser, parseAttributes )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Error
import           Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.Syntax
import           Kore.Syntax.Definition
import qualified Kore.Verified as Verified

verifyAliases
    :: [ParsedSentence]
    -> SentenceVerifier ()
verifyAliases sentences = do
    let aliases =
            Map.fromList . map (\sentence -> (aliasName sentence, sentence))
            $ mapMaybe projectSentenceAlias sentences
        aliasIds = Map.keysSet aliases
    runReaderT
        (Foldable.traverse_ verifyAlias aliasIds)
        AliasContext { aliases, verifying = Set.empty }

aliasName :: SentenceAlias patternType -> Id
aliasName = aliasConstructor . sentenceAliasAlias

type AliasVerifier = ReaderT AliasContext SentenceVerifier

data AliasContext =
    AliasContext
        { aliases   :: !(Map Id ParsedSentenceAlias)
        , verifying :: !(Set Id)
        }
    deriving (GHC.Generic)

type VerifiedAlias = (Attribute.Symbol, SentenceAlias Verified.Pattern)

lookupVerifiedAlias :: Id -> AliasVerifier (Maybe VerifiedAlias)
lookupVerifiedAlias name = do
    verifiedAliases <- State.gets indexedModuleAliasSentences
    return $ Map.lookup name verifiedAliases

lookupParsedAlias :: Id -> AliasVerifier ParsedSentenceAlias
lookupParsedAlias name =
    Reader.asks (Map.lookup name . aliases) >>= maybe notFound return
  where
    notFound = koreFail "Alias not found."

verifyAlias :: Id -> AliasVerifier ()
verifyAlias name =
    withLocationAndContext name aliasContext $ do
        checkAliasCycle
        lookupVerifiedAlias name >>= maybe notCached cached
  where
    aliasContext = "alias '" <> getId name <> "' declaration"
    checkAliasCycle = do
        isCycle <- Reader.asks (Set.member name . verifying)
        koreFailWhen isCycle "Circular alias dependency."
    cached _ = return ()
    notCached = verifyUncachedAlias name

verifyUncachedAlias :: Id -> AliasVerifier ()
verifyUncachedAlias name = do
    sentence <- lookupParsedAlias name
    dependencies <- aliasDependencies sentence
    Foldable.traverse_ verifyAlias dependencies
    verified <- SentenceVerifier.verifyAliasSentence sentence & Trans.lift
    attrs <- parseAttributes (sentenceAliasAttributes verified) & liftParser
    State.modify' $ addAlias verified attrs
  where
    addAlias verified attrs =
        Lens.over
            (field @"indexedModuleAliasSentences")
            (Map.insert (aliasName verified) (attrs, verified))

aliasDependencies :: SentenceAlias ParsedPattern -> AliasVerifier (Set Id)
aliasDependencies = Recursive.fold collectAliasIds . sentenceAliasRightPattern

collectAliasIds
    :: Base ParsedPattern (AliasVerifier (Set Id))
    -> AliasVerifier (Set Id)
collectAliasIds base = do
    _ :< patternF <- sequence base
    let names = Foldable.fold patternF
    AliasContext { aliases } <- Reader.ask
    case patternF of
        ApplicationF application | Map.member name aliases ->
            return $ Set.insert name names
          where
            name =
                symbolOrAliasConstructor
                . applicationSymbolOrAlias
                $ application
        _ -> return names
