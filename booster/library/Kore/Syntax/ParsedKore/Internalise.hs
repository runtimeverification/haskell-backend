{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Converts a @ParsedDefinition@ to a @KoreDefinition@, extracting all
data needed internally from the parsed entities.
-}
module Kore.Syntax.ParsedKore.Internalise (
    buildDefinition,
    DefinitionError (..),
) where

import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Bifunctor (first)
import Data.Function (on)
import Data.List (groupBy, partition, sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)

import Kore.Definition.Attributes.Base
import Kore.Definition.Attributes.Reader
import Kore.Definition.Base as Def
import Kore.Pattern.Base qualified as Def
import Kore.Syntax.Json.Base qualified as Json
import Kore.Syntax.Json.Internalise
import Kore.Syntax.ParsedKore.Base

{- | Traverses all modules of a parsed definition, to build an internal
@KoreDefinition@. Traversal starts on the given module name if
present, otherwise it starts at the last module in the file ('kompile'
default).

Only very few validations are performed on the parsed data.
-}
buildDefinition :: Maybe Text -> ParsedDefinition -> Except DefinitionError KoreDefinition
buildDefinition mbMainModule def@ParsedDefinition{modules} =
    definition
        <$> execStateT (descendFrom mainModule) State{moduleMap, definition = start}
  where
    mainModule = fromMaybe (moduleName $ last modules) mbMainModule
    moduleMap = Map.fromList [(moduleName m, m) | m <- modules]
    start = emptyKoreDefinition (extract def)

{- | The state while traversing the module import graph. This is
 internal only, but the definition is the result of the traversal.
-}
data DefinitionState = State
    { moduleMap :: Map Text ParsedModule
    , definition :: KoreDefinition
    }

{- | Traverses the import graph bottom up, ending in the given named
   module. All entities (sorts, symbols, axioms) that are in scope in
   that module are added to the definition.
-}
descendFrom :: Text -> StateT DefinitionState (Except DefinitionError) ()
descendFrom m = do
    State{moduleMap, definition = currentDef} <- get
    case Map.lookup m (Def.modules currentDef) of
        Just _ -> pure () -- already internalised (present in the definition)
        Nothing -> do
            let mbModule = Map.lookup m moduleMap
            theModule <- maybe (defError $ NoSuchModule m) pure mbModule

            -- traverse imports recursively in pre-order before
            -- dealing with the current module.
            --
            -- NB that this is not exactly the imported context,
            -- though: in recursive calls when handling an imported
            -- module, other modules may be in the current definition
            -- which are not actually imported in that submodule
            mapM_ (descendFrom . fromJsonId . fst) $ imports theModule

            -- refresh current definition
            def <- gets definition

            -- validate and add new module in context of the existing
            -- definition
            newDef <- addModule theModule def
            modify $ \s -> s{definition = newDef}

-- | currently no validations are performed
addModule ::
    ParsedModule ->
    KoreDefinition ->
    StateT DefinitionState (Except DefinitionError) KoreDefinition
addModule
    m@ParsedModule
        { name = Json.Id n
        , sorts = parsedSorts
        , symbols = parsedSymbols
        , axioms = _parsedAxioms
        }
    KoreDefinition
        { attributes
        , modules = currentModules
        , sorts = currentSorts
        , symbols = currentSymbols
        , axioms = currentAxioms
        } =
        do
            --
            when (n `Map.member` currentModules) $
                error "internal error while loading: traversing module twice"
            let modules = Map.insert n (extract m) currentModules

            -- ensure sorts are unique and only refer to known other sorts
            -- TODO, will need sort attributes to determine sub-sorts

            let (newSorts, sortDups) = parsedSorts `mappedBy` sortName
            unless (null sortDups) $
                defError $
                    DuplicateSorts (concatMap snd sortDups)
            let sortCollisions :: [ParsedSort]
                sortCollisions =
                    Map.elems $ Map.intersection newSorts currentSorts
            unless (null sortCollisions) $
                defError $
                    DuplicateSorts sortCollisions
            let sorts = Map.map extract newSorts <> currentSorts

            -- ensure parsed symbols are not duplicates and only refer
            -- to known sorts
            let (newSymbols, symDups) = parsedSymbols `mappedBy` symbolName
                symCollisions =
                    Map.elems $ Map.intersection newSymbols currentSymbols
            unless (null symDups) $
                defError $
                    DuplicateSymbols (concatMap snd symDups)
            unless (null symCollisions) $
                defError $
                    DuplicateSymbols symCollisions
            -- internalise (in a new pass over the list)
            let internaliseSymbol ::
                    ParsedSymbol ->
                    StateT s (Except DefinitionError) (Def.SymbolName, (SymbolAttributes, SymbolSort))
                internaliseSymbol s@ParsedSymbol{name} = do
                    info <- mkSymbolSorts sorts s
                    pure (fromJsonId name, (extract s, info))
            newSymbols' <- mapM internaliseSymbol parsedSymbols
            let symbols = Map.fromList newSymbols' <> currentSymbols

            pure
                KoreDefinition
                    { attributes
                    , modules
                    , sorts
                    , symbols
                    , axioms = currentAxioms -- FIXME
                    }
      where
        -- returns the
        mappedBy ::
            forall a k.
            (Ord k) =>
            [a] ->
            (a -> k) ->
            (Map k a, [(k, [a])])
        things `mappedBy` getKey =
            let sorted :: [[a]]
                sorted = groupBy ((==) `on` getKey) $ sortOn getKey things
                (good, dups) = partition (null . tail) sorted
             in ( Map.fromAscList [(getKey a, a) | [a] <- good]
                , [(getKey $ head d, d) | d <- dups]
                )

defError :: DefinitionError -> StateT s (Except DefinitionError) a
defError = lift . throwE

{- | Checks if a given parsed symbol uses only sorts from the provided
   sort map, and whether they are consistent (wrt. sort parameter
   count), and returns a @SymbolSort@ (sort information record) for
   the symbol.
-}
mkSymbolSorts ::
    Map Def.SortName SortAttributes ->
    ParsedSymbol ->
    StateT s (Except DefinitionError) SymbolSort
mkSymbolSorts sortMap ParsedSymbol{sortVars, argSorts = sorts, sort} =
    do
        unless (Set.size knownVars == length sortVars) $
            defError $
                DuplicateNames (map fromJsonId sortVars)
        resultSort <- lift $ check sort
        argSorts <- mapM (lift . check) sorts
        pure $ SymbolSort{resultSort, argSorts}
  where
    knownVars = Set.fromList $ map fromJsonId sortVars

    check :: Json.Sort -> Except DefinitionError Def.Sort
    check =
        mapExcept (first DefinitionSortError)
            . checkSort knownVars sortMap

-- monomorphic name functions for different entities (avoiding field
-- name ambiguity)
moduleName :: ParsedModule -> Text
moduleName ParsedModule{name = Json.Id n} = n

sortName :: ParsedSort -> Text
sortName ParsedSort{name} = fromJsonId name

symbolName :: ParsedSymbol -> Text
symbolName ParsedSymbol{name} = fromJsonId name

fromJsonId :: Json.Id -> Text
fromJsonId (Json.Id n) = n

----------------------------------------
data DefinitionError
    = ParseError Text
    | NoSuchModule Text
    | DuplicateSorts [ParsedSort]
    | DuplicateSymbols [ParsedSymbol]
    | DuplicateNames [Text]
    | DefinitionSortError SortError
    deriving stock (Eq, Show)
