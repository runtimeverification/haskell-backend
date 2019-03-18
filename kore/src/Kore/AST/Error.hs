{-|
Module      : Kore.AST.Error
Description : Extensions for errors related to the AST.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.AST.Error
    ( koreFailWithLocations
    , koreFailWithLocationsWhen
    , withLocationAndContext
    , withLocationsContext
    , withSentenceAliasContext
    , withSentenceAxiomContext
    , withSentenceClaimContext
    , withSentenceHookContext
    , withSentenceImportContext
    , withSentenceSortContext
    , withSentenceSymbolContext
    , withSentenceContext

    , noSort
    , noHead
    , noAlias
    , noSymbol
    ) where

import Data.List
       ( intercalate )

import Kore.AST.AstWithLocation
import Kore.AST.Common
       ( SymbolOrAlias )
import Kore.AST.Kore
import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.Sentence
import Kore.Error

{-|'koreFailWithLocations' produces an error result with a context containing
the provided locations. -}
koreFailWithLocations
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => [astWithLocation]
    -> String
    -> m a
koreFailWithLocations locations errorMessage =
    withLocationsContext locations (koreFail errorMessage)

{-|'koreFailWithLocationsWhen' produces an error result with a context
containing the provided locations whenever the provided flag is true.
-}
koreFailWithLocationsWhen
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => Bool
    -> [astWithLocation]
    -> String
    -> m ()
koreFailWithLocationsWhen condition locations errorMessage =
    withLocationsContext locations (koreFailWhen condition errorMessage)

{-|'withLocationsContext' prepends the given location to the error context
whenever the given action fails.
-}
withLocationsContext
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => [astWithLocation]
    -> m result
    -> m result
withLocationsContext locations =
    withContext
        (  "("
        ++ intercalate ", " (map prettyPrintLocationFromAst locations)
        ++ ")"
        )

{-|'withLocationsContext' prepends the given message, associated with the
location, to the error context whenever the given action fails.
-}
withLocationAndContext
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => astWithLocation
    -> String
    -> m result
    -> m result
withLocationAndContext location message =
    withContext (message ++ " (" ++ prettyPrintLocationFromAst location ++ ")")

{- | Identify and locate the given symbol declaration in the error context.
 -}
withSentenceSymbolContext
    :: MonadError (Error e) m
    => SentenceSymbol level patternType
    -> m a
    -> m a
withSentenceSymbolContext
    SentenceSymbol { sentenceSymbolSymbol = Symbol { symbolConstructor } }
  =
    withLocationAndContext symbolConstructor
        ("symbol '" ++ getIdForError symbolConstructor ++ "' declaration")

{- | Identify and locate the given alias declaration in the error context.
 -}
withSentenceAliasContext
    :: SentenceAlias level patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceAliasContext
    SentenceAlias { sentenceAliasAlias = Alias { aliasConstructor } }
  =
    withLocationAndContext aliasConstructor
        ("alias '" ++ getIdForError aliasConstructor ++ "' declaration")

{- | Identify and locate the given axiom declaration in the error context.
 -}
withSentenceAxiomContext
    :: SentenceAxiom sortParam patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceAxiomContext _ = withContext "axiom declaration"

{- | Identify and locate the given claim declaration in the error context.
 -}
withSentenceClaimContext
    :: SentenceAxiom sortParam patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceClaimContext _ = withContext "claim declaration"

{- | Identify and locate the given sort declaration in the error context.
 -}
withSentenceSortContext
    :: SentenceSort level patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceSortContext
    SentenceSort { sentenceSortName }
  =
    withLocationAndContext sentenceSortName
        ("sort '" ++ getIdForError sentenceSortName ++ "' declaration")

{- | Identify and locate the given hooked declaration in the error context.
 -}
withSentenceHookContext
    :: SentenceHook patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceHookContext =
    \case
        SentenceHookedSort SentenceSort { sentenceSortName } ->
            withLocationAndContext sentenceSortName
                ("hooked-sort '" ++ getIdForError sentenceSortName ++ "' declaration")

        SentenceHookedSymbol SentenceSymbol
            { sentenceSymbolSymbol = Symbol { symbolConstructor } } ->
            withLocationAndContext symbolConstructor
                ("hooked-symbol '" ++ getIdForError symbolConstructor ++ "' declaration")

{- | Locate the given import declaration in the error context.
 -}
withSentenceImportContext
    :: SentenceImport patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceImportContext _ = \go -> go

{- | Identify and  locate the given sentence in the error context.
 -}
withSentenceContext
    :: Sentence level sortParam patternType
    -> Either (Error e) a
    -> Either (Error e) a
withSentenceContext =
    \case
        SentenceAliasSentence s -> withSentenceAliasContext s
        SentenceAxiomSentence s -> withSentenceAxiomContext s
        SentenceClaimSentence s -> withSentenceClaimContext s
        SentenceHookSentence s -> withSentenceHookContext s
        SentenceImportSentence s -> withSentenceImportContext s
        SentenceSortSentence s -> withSentenceSortContext s
        SentenceSymbolSentence s -> withSentenceSymbolContext s

{- Support for warning of undefined values -}

-- | A message declaring that a Sort is undefined
noSort :: MetaOrObject level => Id level -> String
noSort sortId =
    notDefined "Sort" $ show sortId

-- | A message declaring that a Head is undefined
noHead :: MetaOrObject level => SymbolOrAlias level -> String
noHead patternHead =
    notDefined "Head" $ show patternHead

-- | A message declaring that a Alias is undefined
noAlias :: MetaOrObject level => Id level -> String
noAlias identifier =
    notDefined "Alias" $ getIdForError identifier

-- | A message declaring that a Symbol is undefined
noSymbol :: MetaOrObject level => Id level -> String
noSymbol identifier =
    notDefined "Symbol" $ getIdForError identifier
