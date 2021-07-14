{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Validate.AliasVerifier (verifyAliases) where

import qualified Control.Lens as Lens
import Control.Monad.Reader (
    ReaderT,
    runReaderT,
 )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Class as State
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC
import Kore.AST.Error
import Kore.Attribute.Parser (
    liftParser,
    parseAttributes,
 )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Validate.SentenceVerifier (
    SentenceVerifier,
 )
import qualified Kore.Validate.SentenceVerifier as SentenceVerifier
import qualified Kore.Verified as Verified
import Prelude.Kore

{- | Project the 'SentenceAlias'es from the list and verify them.

The verified aliases are added to the current 'VerifiedModule'. The aliases are
verified in the order they occur in the list, except that the dependencies of
each alias are verified before itself.

It is an error if any alias if it depends on itself (directly, or in a cycle
through another alias).
-}
verifyAliases ::
    [ParsedSentence] ->
    SentenceVerifier ()
verifyAliases sentences = do
    let aliases =
            Map.fromList . map (\sentence -> (aliasName sentence, sentence)) $
                mapMaybe projectSentenceAlias sentences
        aliasIds = Map.keysSet aliases
    runReaderT
        (traverse_ verifyAlias aliasIds)
        AliasContext{aliases, verifying = Set.empty}

aliasName :: SentenceAlias patternType -> Id
aliasName = aliasConstructor . sentenceAliasAlias

type AliasVerifier = ReaderT AliasContext SentenceVerifier

data AliasContext = AliasContext
    { aliases :: !(Map Id ParsedSentenceAlias)
    , verifying :: !(Set Id)
    }
    deriving stock (GHC.Generic)

type VerifiedAlias = (Attribute.Symbol, SentenceAlias Verified.Pattern)

-- | Look up a 'VerifiedAlias' in the cache, if present.
lookupVerifiedAlias :: Id -> AliasVerifier (Maybe VerifiedAlias)
lookupVerifiedAlias name = do
    verifiedAliases <- State.gets indexedModuleAliasSentences
    return $ Map.lookup name verifiedAliases

{- | Lookup a 'ParsedSentencAlias' in the current module.

It is an error if the alias is missing.
-}
lookupParsedAlias :: Id -> AliasVerifier ParsedSentenceAlias
lookupParsedAlias name =
    Reader.asks (Map.lookup name . aliases) >>= maybe notFound return
  where
    notFound = koreFail "Alias not found."

{- | Verify and add the named alias to the current module.

The alias is fetched from the cache, if available; otherwise is is verified and
cached.
-}
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

-- | Verify the named alias without using the cache.
verifyUncachedAlias :: Id -> AliasVerifier ()
verifyUncachedAlias name = do
    sentence <- lookupParsedAlias name
    dependencies <- aliasDependencies sentence
    traverse_ verifyAlias dependencies
    verified <- SentenceVerifier.verifyAliasSentence sentence & lift
    attrs <- parseAttributes (sentenceAliasAttributes verified) & liftParser
    State.modify' $ addAlias verified attrs
  where
    addAlias verified attrs =
        Lens.over
            (field @"indexedModuleAliasSentences")
            (Map.insert (aliasName verified) (attrs, verified))

-- | Determine the names of all aliases the 'ParsedSentenceAlias' depends on.
aliasDependencies :: ParsedSentenceAlias -> AliasVerifier (Set Id)
aliasDependencies = Recursive.fold collectAliasIds . sentenceAliasRightPattern

-- | Collect the names of all aliases which a pattern depends on.
collectAliasIds ::
    Base ParsedPattern (AliasVerifier (Set Id)) ->
    AliasVerifier (Set Id)
collectAliasIds base = do
    _ :< patternF <- sequence base
    let names = fold patternF
    AliasContext{aliases} <- Reader.ask
    case patternF of
        ApplicationF application
            | Map.member name aliases ->
                return $ Set.insert name names
          where
            name =
                symbolOrAliasConstructor
                    . applicationSymbolOrAlias
                    $ application
        _ -> return names
