{-# LANGUAGE OverloadedStrings #-}

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
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)

import Kore.Definition.Attributes.Reader
import Kore.Definition.Base as Def
import Kore.Syntax.Json.Base (Id (..))
import Kore.Syntax.ParsedKore.Base

{- | Traverses all modules of a parsed definition, to build an
internal @KoreDefinition@.

Only very few validations are performed on the parsed data.
-}
buildDefinition :: ParsedDefinition -> Except DefinitionError KoreDefinition
buildDefinition def@ParsedDefinition{modules} =
    traverseModules modules $ emptyKoreDefinition (extract def)

{- | The state while traversing the module import graph. This is
 internal only, but the definition is the result of the traversal.
-}
data DefinitionState = State
    { moduleMap :: Map Text ParsedModule
    , definition :: KoreDefinition
    }

traverseModules ::
    [ParsedModule] ->
    KoreDefinition ->
    Except DefinitionError KoreDefinition
traverseModules modules start =
    definition
        <$> execStateT (descendFrom mainModule) State{moduleMap, definition = start}
  where
    moduleMap = Map.fromList [(moduleName m, m) | m <- modules]
    mainModule = moduleName $ last modules -- just by convention
    moduleName :: ParsedModule -> Text
    moduleName ParsedModule{name = Id n} = n

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
            theModule <- maybe (lift . throwE $ NoSuchModule m) pure mbModule

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

fromJsonId :: Id -> Text
fromJsonId (Id n) = n

-- | currently no validations are performed
addModule ::
    ParsedModule ->
    KoreDefinition ->
    StateT DefinitionState (Except DefinitionError) KoreDefinition
addModule
    m@ParsedModule
        { name = Id n
        , sorts = parsedSorts
        , symbols = _parsedSymbols
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
            let newSorts =
                    Map.fromList
                        [ (fromJsonId sortName, sort)
                        | sort@ParsedSort{name = sortName} <- parsedSorts
                        ]
                nameCollisions :: [ParsedSort]
                nameCollisions =
                    Map.elems $ Map.intersection newSorts currentSorts
            unless (null nameCollisions) $
                lift . throwE $
                    DuplicateSorts nameCollisions
            let sorts = Map.map extract newSorts <> currentSorts

            pure
                KoreDefinition
                    { attributes
                    , modules
                    , sorts
                    , symbols = currentSymbols -- FIXME
                    , axioms = currentAxioms -- FIXME
                    }

----------------------------------------
data DefinitionError
    = GeneralError Text
    | NoSuchModule Text
    | DuplicateSorts [ParsedSort]
