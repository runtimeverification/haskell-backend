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
import Data.List.Extra (groupSort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text

import Kore.Definition.Attributes.Base
import Kore.Definition.Attributes.Reader
import Kore.Definition.Base as Def
import Kore.Pattern.Base qualified as Def
import Kore.Pattern.Util qualified as Util
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
            mapM_ (descendFrom . Json.getId . fst) $ imports theModule

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
        , aliases = parsedAliases
        , axioms = parsedAxioms
        }
    KoreDefinition
        { attributes
        , modules = currentModules
        , sorts = currentSorts
        , symbols = currentSymbols
        , aliases = currentAliases
        , rewriteTheory = currentRewriteTheory
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
                    -- TODO(Ana): rename extract
                    pure (Json.getId name, (extract s, info))
            newSymbols' <- mapM internaliseSymbol parsedSymbols
            let symbols = Map.fromList newSymbols' <> currentSymbols

            let internaliseAlias ::
                    ParsedAlias ->
                    StateT s (Except DefinitionError) (Def.AliasName, Alias)
                -- TODO(Ana): do we need to handle attributes?
                internaliseAlias palias@ParsedAlias{name, sortVars, argSorts, sort, args, rhs} = lift $ do
                    unless (length argSorts == length args) (throwE (DefinitionAliasError (Json.getId name) . WrongAliasSortCount $ palias))
                    let paramNames = Json.getId <$> sortVars
                        params = Def.SortVar <$> paramNames
                        argNames = Json.getId <$> args
                        internalName = Json.getId name
                    internalArgSorts <- traverse (withExcept DefinitionSortError . checkSort (Set.fromList paramNames) sorts) argSorts
                    internalResSort <- withExcept DefinitionSortError $ checkSort (Set.fromList paramNames) sorts sort
                    let internalArgs = uncurry Def.Variable <$> zip internalArgSorts argNames
                    let partialDefinition = KoreDefinition{attributes, modules, sorts, symbols, aliases = currentAliases, rewriteTheory = currentRewriteTheory}
                    internalRhs <-
                        withExcept (DefinitionAliasError (Json.getId name) . InconsistentAliasPattern) $
                            internaliseTermOrPredicate (Just sortVars) partialDefinition rhs
                    let rhsSort = Util.sortOfTermOrPredicate internalRhs
                    unless (fromMaybe internalResSort rhsSort == internalResSort) (throwE (DefinitionSortError (GeneralError "IncompatibleSorts")))
                    return (internalName, Alias{name = internalName, params, args = internalArgs, rhs = internalRhs})
                -- filter out "antiLeft" aliases, recognised by name and argument count
                notPriority ParsedAlias{name = Json.Id alias, args} =
                    not $ null args && "priority" `Text.isPrefixOf` alias
            newAliases <- traverse internaliseAlias $ filter notPriority parsedAliases
            let aliases = Map.fromList newAliases <> currentAliases

            let partialDefinition = KoreDefinition{attributes, modules, sorts, symbols, aliases, rewriteTheory = currentRewriteTheory}

            -- TODO(Ana): this should return a sum type of different kinds of information
            -- regarding the theory: rewrite rules (which we apply), subsort relationships, other
            -- things that are encoded into Kore as axioms
            let internaliseRewriteTheoryData ::
                    ParsedAxiom ->
                    StateT s (Except DefinitionError) (Maybe RewriteRule)
                internaliseRewriteTheoryData parsedAx@ParsedAxiom{axiom} = lift $ do
                    case axiom of
                        Json.KJRewrites _ left right ->
                            case left of
                                Json.KJAnd _ (Json.KJNot _ _) (Json.KJApp (Json.Id aliasName) _ aliasArgs) ->
                                    Just <$> internaliseRewriteRule partialDefinition parsedAx aliasName aliasArgs right
                                (Json.KJApp (Json.Id aliasName) _ aliasArgs) ->
                                    Just <$> internaliseRewriteRule partialDefinition parsedAx aliasName aliasArgs right
                                _ -> throwE (DefinitionRewriteRuleError . MalformedRewriteRule $ parsedAx)
                        _ -> return Nothing

            newRewriteRules <- catMaybes <$> traverse internaliseRewriteTheoryData parsedAxioms
            let rewriteTheory = addToTheory newRewriteRules currentRewriteTheory

            pure
                KoreDefinition
                    { attributes
                    , modules
                    , sorts
                    , symbols
                    , aliases
                    , rewriteTheory
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

orFailWith :: Maybe a -> e -> Except e a
mbX `orFailWith` err = maybe (throwE err) pure mbX

internaliseRewriteRule ::
    KoreDefinition ->
    ParsedAxiom ->
    AliasName ->
    [Json.KorePattern] ->
    Json.KorePattern ->
    Except DefinitionError RewriteRule
internaliseRewriteRule partialDefinition@KoreDefinition{aliases} parsedAx@ParsedAxiom{sortVars} aliasName aliasArgs right = do
    alias <-
        withExcept (DefinitionAliasError aliasName) $
            Map.lookup aliasName aliases
                `orFailWith` UnknownAlias aliasName
    args <- traverse (withExcept DefinitionPatternError . internaliseTerm (Just sortVars) partialDefinition) aliasArgs
    result <- expandAlias alias args
    lhs <-
        Util.retractPattern result
            `orFailWith` DefinitionTermOrPredicateError (PatternExpected result)
    rhs <-
        withExcept DefinitionPatternError $
            internalisePattern (Just sortVars) partialDefinition right
    let axAttributes = extract parsedAx
    return RewriteRule{lhs, rhs, attributes = axAttributes}

defError :: DefinitionError -> StateT s (Except DefinitionError) a
defError = lift . throwE

expandAlias :: Alias -> [Def.Term] -> Except DefinitionError Def.TermOrPredicate
expandAlias alias@Alias{name, args, rhs} currentArgs
    | length args /= length currentArgs = throwE (DefinitionAliasError name $ WrongAliasArgCount alias currentArgs)
    | otherwise =
        let substitution = Map.fromList (zip args currentArgs)
         in return $ substitute substitution rhs
  where
    substitute substitution termOrPredicate =
        case termOrPredicate of
            Def.APredicate predicate ->
                Def.APredicate $ substituteInPredicate substitution predicate
            Def.TermAndPredicate Def.Pattern{term, constraints} ->
                Def.TermAndPredicate
                    Def.Pattern
                        { term = substituteInTerm substitution term
                        , constraints =
                            substituteInPredicate substitution <$> constraints
                        }

    substituteInTerm substitution term =
        case term of
            Def.AndTerm sort t1 t2 ->
                Def.AndTerm sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
            Def.SymbolApplication sort sorts symname sargs ->
                Def.SymbolApplication sort sorts symname (substituteInTerm substitution <$> sargs)
            dv@(Def.DomainValue _ _) -> dv
            v@(Def.Var var) ->
                fromMaybe v (Map.lookup var substitution)

    substituteInPredicate substitution predicate =
        case predicate of
            Def.AndPredicate p1 p2 ->
                Def.AndPredicate (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
            Def.Bottom -> Def.Bottom
            Def.Ceil t -> Def.Ceil (substituteInTerm substitution t)
            Def.EqualsTerm sort t1 t2 ->
                Def.EqualsTerm sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
            Def.EqualsPredicate p1 p2 ->
                Def.EqualsPredicate (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
            Def.Exists v p ->
                Def.Exists v (substituteInPredicate substitution p)
            Def.Forall v p ->
                Def.Forall v (substituteInPredicate substitution p)
            Def.Iff p1 p2 ->
                Def.Iff (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
            Def.Implies p1 p2 ->
                Def.Implies (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
            Def.In sort t1 t2 ->
                Def.In sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
            Def.Not p ->
                Def.Not (substituteInPredicate substitution p)
            Def.Or p1 p2 ->
                Def.Or (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
            Def.Top -> Def.Top

processRewriteRulesTODO :: [RewriteRule] -> [RewriteRule]
processRewriteRulesTODO = id

addToTheory :: [RewriteRule] -> RewriteTheory -> RewriteTheory
addToTheory axioms theory =
    let processedRewriteRules = processRewriteRulesTODO axioms
        newTheory =
            Map.map groupByPriority
                . groupByTermIndex
                $ processedRewriteRules
     in Map.unionWith (Map.unionWith (<>)) theory newTheory

groupByTermIndex :: [RewriteRule] -> Map Def.TermIndex [RewriteRule]
groupByTermIndex axioms =
    let withTermIndexes = do
            axiom@RewriteRule{lhs} <- axioms
            let termIndex = Def.computeTermIndex (Def.term lhs)
            return (termIndex, axiom)
     in Map.fromAscList . groupSort $ withTermIndexes

groupByPriority :: [RewriteRule] -> Map Priority [RewriteRule]
groupByPriority axioms =
    Map.fromAscList . groupSort $ [(extractPriority ax, ax) | ax <- axioms]

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
                DuplicateNames (map Json.getId sortVars)
        resultSort <- lift $ check sort
        argSorts <- mapM (lift . check) sorts
        pure $ SymbolSort{resultSort, argSorts}
  where
    knownVars = Set.fromList $ map Json.getId sortVars

    check :: Json.Sort -> Except DefinitionError Def.Sort
    check =
        mapExcept (first DefinitionSortError)
            . checkSort knownVars sortMap

-- monomorphic name functions for different entities (avoiding field
-- name ambiguity)
moduleName :: ParsedModule -> Text
moduleName ParsedModule{name} = Json.getId name

sortName :: ParsedSort -> Text
sortName ParsedSort{name} = Json.getId name

symbolName :: ParsedSymbol -> Text
symbolName ParsedSymbol{name} = Json.getId name

----------------------------------------
data DefinitionError
    = ParseError Text
    | NoSuchModule Text
    | DuplicateSorts [ParsedSort]
    | DuplicateSymbols [ParsedSymbol]
    | DuplicateAliases [ParsedAlias]
    | DuplicateNames [Text]
    | DefinitionSortError SortError
    | DefinitionPatternError PatternError
    | DefinitionAliasError Text AliasError
    | DefinitionRewriteRuleError RewriteRuleError
    | DefinitionTermOrPredicateError TermOrPredicateError
    deriving stock (Eq, Show)

data AliasError
    = UnknownAlias AliasName
    | WrongAliasSortCount ParsedAlias
    | WrongAliasArgCount Alias [Def.Term]
    | InconsistentAliasPattern [PatternError]
    deriving stock (Eq, Show)

newtype RewriteRuleError
    = MalformedRewriteRule ParsedAxiom
    deriving stock (Eq, Show)

data TermOrPredicateError
    = PatternExpected Def.TermOrPredicate
    | TOPNotSupported Def.TermOrPredicate
    deriving stock (Eq, Show)
