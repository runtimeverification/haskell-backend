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
    , withModuleContext
    ) where

import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Kore.AST.AstWithLocation
import Kore.Error
import Kore.Syntax
import Kore.Syntax.Definition

{-|'koreFailWithLocations' produces an error result with a context containing
the provided locations. -}
koreFailWithLocations
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => [astWithLocation]
    -> Text
    -> m a
koreFailWithLocations locations errorMessage =
    withLocationsContext locations (koreFailText errorMessage)

{-|'koreFailWithLocationsWhen' produces an error result with a context
containing the provided locations whenever the provided flag is true.
-}
koreFailWithLocationsWhen
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => Bool
    -> [astWithLocation]
    -> Text
    -> m ()
koreFailWithLocationsWhen condition locations errorMessage =
    withLocationsContext locations (koreFailWhenText condition errorMessage)

{-|'withLocationsContext' prepends the given location to the error context
whenever the given action fails.
-}
withLocationsContext
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => [astWithLocation]
    -> m result
    -> m result
withLocationsContext locations =
    withTextContext
        (  "("
        <> Text.intercalate ", " (map prettyPrintLocationFromAst locations)
        <> ")"
        )

{-|'withLocationsContext' prepends the given message, associated with the
location, to the error context whenever the given action fails.
-}
withLocationAndContext
    :: (AstWithLocation astWithLocation, MonadError (Error e) m)
    => astWithLocation
    -> Text
    -> m result
    -> m result
withLocationAndContext location message =
    withTextContext
        (message <> " (" <> prettyPrintLocationFromAst location <> ")")

{- | Identify and locate the given symbol declaration in the error context.
 -}
withSentenceSymbolContext
    :: MonadError (Error e) error
    => SentenceSymbol patternType
    -> error a
    -> error a
withSentenceSymbolContext
    SentenceSymbol { sentenceSymbolSymbol = Symbol { symbolConstructor } }
  =
    withLocationAndContext symbolConstructor
        ("symbol '" <> getId symbolConstructor <> "' declaration")

{- | Identify and locate the given alias declaration in the error context.
 -}
withSentenceAliasContext
    :: MonadError (Error e) error
    => SentenceAlias patternType
    -> error a
    -> error a
withSentenceAliasContext
    SentenceAlias { sentenceAliasAlias = Alias { aliasConstructor } }
  =
    withLocationAndContext aliasConstructor
        ("alias '" <> getId aliasConstructor <> "' declaration")

{- | Identify and locate the given axiom declaration in the error context.
 -}
withSentenceAxiomContext
    :: MonadError (Error e) error
    => SentenceAxiom patternType
    -> error a
    -> error a
withSentenceAxiomContext _ = withContext "axiom declaration"

{- | Identify and locate the given claim declaration in the error context.
 -}
withSentenceClaimContext
    :: MonadError (Error e) error
    => SentenceClaim patternType
    -> error a
    -> error a
withSentenceClaimContext _ = withContext "claim declaration"

{- | Identify and locate the given sort declaration in the error context.
 -}
withSentenceSortContext
    :: MonadError (Error e) error
    => SentenceSort patternType
    -> error a
    -> error a
withSentenceSortContext SentenceSort { sentenceSortName } =
    withLocationAndContext sentenceSortName
        ("sort '" <> getId sentenceSortName <> "' declaration")

{- | Identify and locate the given hooked declaration in the error context.
 -}
withSentenceHookContext
    :: MonadError (Error e) error
    => SentenceHook patternType
    -> error a
    -> error a
withSentenceHookContext =
    \case
        SentenceHookedSort SentenceSort { sentenceSortName } ->
            withLocationAndContext sentenceSortName
                (  "hooked-sort '"
                <> getId sentenceSortName
                <> "' declaration"
                )

        SentenceHookedSymbol SentenceSymbol
            { sentenceSymbolSymbol = Symbol { symbolConstructor } } ->
            withLocationAndContext symbolConstructor
                (  "hooked-symbol '"
                <> getId symbolConstructor
                <> "' declaration"
                )

{- | Locate the given import declaration in the error context.
 -}
withSentenceImportContext
    :: MonadError (Error e) error
    => SentenceImport patternType
    -> error a
    -> error a
withSentenceImportContext _ = id

{- | Identify and locate the given sentence in the error context.
 -}
withSentenceContext
    :: MonadError (Error e) error
    => Sentence patternType
    -> error a
    -> error a
withSentenceContext =
    \case
        SentenceAliasSentence s -> withSentenceAliasContext s
        SentenceAxiomSentence s -> withSentenceAxiomContext s
        SentenceClaimSentence s -> withSentenceClaimContext s
        SentenceHookSentence s -> withSentenceHookContext s
        SentenceImportSentence s -> withSentenceImportContext s
        SentenceSortSentence s -> withSentenceSortContext s
        SentenceSymbolSentence s -> withSentenceSymbolContext s

{- | Identify the given module in the error context.
 -}
withModuleContext
    :: MonadError (Error e) error
    => ModuleName
    -> error a
    -> error a
withModuleContext moduleName =
    withContext ("module '" ++ getModuleNameForError moduleName ++ "'")
