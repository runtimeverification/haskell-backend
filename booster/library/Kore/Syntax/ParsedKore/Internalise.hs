{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

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

import Control.Monad.Extra (mapMaybeM)
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Bifunctor (first)
import Data.Function (on)
import Data.List (foldl', groupBy, partition, sortOn)
import Data.List.Extra (groupSort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
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
buildDefinition mbMainModule def@ParsedDefinition{modules} = do
    State{definition = d@KoreDefinition{sorts = allSorts}, subsorts} <-
        execStateT (descendFrom mainModule) startState
    let finalSorts = foldr addSubsortInfo allSorts $ Map.assocs (transitiveClosure subsorts)
        finalDefinition :: KoreDefinition
        finalDefinition = d{sorts = finalSorts}
    pure finalDefinition
  where
    mainModule = fromMaybe (moduleName $ last modules) mbMainModule
    moduleMap = Map.fromList [(moduleName m, m) | m <- modules]
    startState =
        State
            { moduleMap
            , definition = emptyKoreDefinition $ extract def
            , subsorts = Map.empty
            }

    addSubsortInfo ::
        (Def.SortName, Set Def.SortName) ->
        Map Def.SortName (SortAttributes, Set Def.SortName) ->
        Map Def.SortName (SortAttributes, Set Def.SortName)
    addSubsortInfo (super, subs) = Map.update (\(a, b) -> Just (a, b <> subs)) super

-- Some sorts do not occur in the subsort map at all (even though
-- we _should_ have S < KItem for _every_ sort).

{- | The state while traversing the module import graph. This is
 internal only, but the definition is the result of the traversal.
-}
data DefinitionState = State
    { moduleMap :: Map Text ParsedModule
    , definition :: KoreDefinition
    , subsorts :: Map Def.SortName (Set Def.SortName)
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
            theModule <- maybe (lift . throwE $ NoSuchModule m) pure mbModule

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
            (newSubsorts, newDef) <- lift $ addModule theModule def

            modify (updateState newDef newSubsorts)
  where
    updateState :: KoreDefinition -> Map Def.SortName (Set Def.SortName) -> DefinitionState -> DefinitionState
    updateState newDef newSubsorts State{moduleMap, subsorts} =
        State
            { moduleMap
            , definition = newDef
            , subsorts = Map.unionWith (<>) subsorts newSubsorts
            }

-- | currently no validations are performed
addModule ::
    ParsedModule ->
    KoreDefinition ->
    Except DefinitionError (Map Def.SortName (Set Def.SortName), KoreDefinition)
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
                throwE $
                    DuplicateSorts (concatMap snd sortDups)
            let sortCollisions :: [ParsedSort]
                sortCollisions =
                    Map.elems $ Map.intersection newSorts currentSorts
            unless (null sortCollisions) $
                throwE $
                    DuplicateSorts sortCollisions
            let sorts =
                    Map.map (\s -> (extract s, Set.singleton (sortName s))) newSorts
                        <> currentSorts

            -- ensure parsed symbols are not duplicates and only refer
            -- to known sorts
            let (newSymbols, symDups) = parsedSymbols `mappedBy` symbolName
                symCollisions =
                    Map.elems $ Map.intersection newSymbols currentSymbols
            unless (null symDups) $
                throwE $
                    DuplicateSymbols (concatMap snd symDups)
            unless (null symCollisions) $
                throwE $
                    DuplicateSymbols symCollisions
            -- internalise (in a new pass over the list)
            let internaliseSymbol ::
                    ParsedSymbol ->
                    Except DefinitionError (Def.SymbolName, (SymbolAttributes, SymbolSort))
                internaliseSymbol s@ParsedSymbol{name} = do
                    info <- mkSymbolSorts sorts s
                    -- TODO(Ana): rename extract
                    pure (Json.getId name, (extract s, info))
            newSymbols' <- mapM internaliseSymbol parsedSymbols
            let symbols = Map.fromList newSymbols' <> currentSymbols

            let internaliseAlias ::
                    ParsedAlias ->
                    Except DefinitionError (Def.AliasName, Alias)
                -- TODO(Ana): do we need to handle attributes?
                internaliseAlias palias@ParsedAlias{name, sortVars, argSorts, sort, args, rhs} = do
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

            (newRewriteRules, subsortPairs) <-
                partitionAxioms
                    <$> mapMaybeM (internaliseAxiom partialDefinition) parsedAxioms

            let rewriteTheory = addToTheory newRewriteRules currentRewriteTheory

            -- add subsorts to the subsort map
            let newSubsorts =
                    Map.fromListWith
                        (<>)
                        [(super, Set.singleton sub) | (sub, super) <- subsortPairs]

            pure
                ( newSubsorts
                , KoreDefinition
                    { attributes
                    , modules
                    , sorts
                    , symbols
                    , aliases
                    , rewriteTheory
                    }
                )
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

        partitionAxioms :: [AxiomResult] -> ([RewriteRule], [(Def.SortName, Def.SortName)])
        partitionAxioms = go [] []
          where
            go rules sorts [] = (rules, sorts)
            go rules sorts (RewriteRuleAxiom r : rest) = go (r : rules) sorts rest
            go rules sorts (SubsortAxiom pair : rest) = go rules (pair : sorts) rest

-- Result type from internalisation of different axioms
data AxiomResult
    = -- | Rewrite rule
      RewriteRuleAxiom RewriteRule
    | -- | subsort data: a pair of sorts
      SubsortAxiom (Def.SortName, Def.SortName)

-- helper type to carry relevant extracted data from a pattern (what
-- is passed to the internalising function later)
data AxiomData
    = RewriteRuleAxiom' AliasName [Json.KorePattern] Json.KorePattern AxiomAttributes [Json.Id]
    | SubsortAxiom' Json.Sort Json.Sort

classifyAxiom :: ParsedAxiom -> Except DefinitionError (Maybe AxiomData)
classifyAxiom parsedAx@ParsedAxiom{axiom, sortVars} = case axiom of
    -- rewrite: an actual rewrite rule
    Json.KJRewrites _ lhs rhs
        | Json.KJAnd _ (Json.KJNot _ _) (Json.KJApp (Json.Id aliasName) _ aliasArgs) <- lhs ->
            pure $ Just $ RewriteRuleAxiom' aliasName aliasArgs rhs (extract parsedAx) sortVars
        | Json.KJApp (Json.Id aliasName) _ aliasArgs <- lhs ->
            pure $ Just $ RewriteRuleAxiom' aliasName aliasArgs rhs (extract parsedAx) sortVars
        | otherwise ->
            throwE $ DefinitionRewriteRuleError $ MalformedRewriteRule parsedAx
    -- subsort axiom formulated as an existential rule
    Json.KJExists{var, varSort = super, arg}
        | Json.KJEquals{first = aVar, second} <- arg
        , aVar == Json.KJEVar{name = var, sort = super}
        , Json.KJApp{name, args} <- second
        , Json.Id "inj" <- name
        , [Json.KJEVar{name = _, sort = sub}] <- args ->
            pure $ Just $ SubsortAxiom' sub super
    -- implies: an equation
    Json.KJImplies{} ->
        pure Nothing -- not handled yet

    -- anything else: not handled yet but not an error (this case
    -- becomes an error if the list becomes comprehensive)
    _ -> pure Nothing

internaliseAxiom ::
    KoreDefinition ->
    ParsedAxiom ->
    Except DefinitionError (Maybe AxiomResult)
internaliseAxiom partialDefinition parsedAxiom =
    classifyAxiom parsedAxiom >>= maybe (pure Nothing) processAxiom
  where
    processAxiom :: AxiomData -> Except DefinitionError (Maybe AxiomResult)
    processAxiom = \case
        SubsortAxiom' Json.SortApp{name = Json.Id sub} Json.SortApp{name = Json.Id super} -> do
            when (sub == super) $
                throwE $
                    DefinitionSortError $
                        GeneralError ("Bad subsort rule " <> sub <> " < " <> super)
            pure $ Just $ SubsortAxiom (sub, super)
        SubsortAxiom' Json.SortVar{name = Json.Id sub} _ ->
            throwE $
                DefinitionSortError $
                    GeneralError ("Sort variable " <> sub <> " in subsort axiom")
        SubsortAxiom' _ Json.SortVar{name = Json.Id super} ->
            throwE $
                DefinitionSortError $
                    GeneralError ("Sort variable " <> super <> " in subsort axiom")
        RewriteRuleAxiom' alias args rhs attribs sortVars ->
            Just . RewriteRuleAxiom
                <$> internaliseRewriteRule partialDefinition alias args rhs attribs sortVars

orFailWith :: Maybe a -> e -> Except e a
mbX `orFailWith` err = maybe (throwE err) pure mbX

internaliseRewriteRule ::
    KoreDefinition ->
    AliasName ->
    [Json.KorePattern] ->
    Json.KorePattern ->
    AxiomAttributes ->
    [Json.Id] ->
    Except DefinitionError RewriteRule
internaliseRewriteRule partialDefinition@KoreDefinition{aliases} aliasName aliasArgs right axAttributes sortVars = do
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
    return RewriteRule{lhs, rhs, attributes = axAttributes}

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
    Map Def.SortName (SortAttributes, Set Def.SortName) ->
    ParsedSymbol ->
    Except DefinitionError SymbolSort
mkSymbolSorts sortMap ParsedSymbol{sortVars, argSorts = sorts, sort} =
    do
        unless (Set.size knownVars == length sortVars) $
            throwE $
                DuplicateNames (map Json.getId sortVars)
        resultSort <- check sort
        argSorts <- mapM check sorts
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

{- | Computes all-pairs reachability in a directed graph given as an
   adjacency list mapping. Internally uses Warshall's algorithm but
   converts the result back to a reachability list.
-}
transitiveClosure :: forall k. (Ord k) => Map k (Set.Set k) -> Map k (Set.Set k)
transitiveClosure adjacencies = toAdjacencies $ foldl' update matrix allKeys
  where
    allKeys = Map.keys adjacencies

    matrix :: Map (k, k) Bool
    matrix =
        Map.fromList
            [ ((a, b), a == b || (maybe False (b `Set.member`) $ Map.lookup a adjacencies))
            | a <- allKeys
            , b <- allKeys
            ]

    toAdjacencies :: Map (k, k) Bool -> Map k (Set.Set k)
    toAdjacencies matrix' =
        Map.fromListWith
            (<>)
            [(a, Set.singleton b) | ((a, b), True) <- Map.assocs matrix']

    update :: Map (k, k) Bool -> k -> Map (k, k) Bool
    update matrix' k =
        let newPath :: k -> k -> Map (k, k) Bool -> Bool
            newPath a b m = fromMaybe False $ liftM2 (&&) (Map.lookup (a, k) m) (Map.lookup (k, b) m)
            upd m (a, b) = Map.update (Just . (|| newPath a b m)) (a, b) m
         in foldl upd matrix' $ [(x, x') | x <- allKeys, x' <- allKeys]

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
