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

import Control.Applicative (Alternative (..), asum)
import Control.Monad
import Control.Monad.Extra (mapMaybeM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
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
    endState <- execStateT (descendFrom mainModule) startState
    let mainDef = expectPresent mainModule endState.definitionMap
        finalSorts =
            foldr addSubsortInfo mainDef.sorts $
                Map.assocs (transitiveClosure endState.subsorts)
    pure (mainDef{sorts = finalSorts} :: KoreDefinition)
  where
    mainModule = fromMaybe (last modules).name.getId mbMainModule
    moduleMap = Map.fromList [(m.name.getId, m) | m <- modules]
    startState =
        State
            { moduleMap
            , definitionMap = Map.empty
            , definitionAttributes = extract def
            , subsorts = Map.empty
            }
    addSubsortInfo ::
        (Def.SortName, Set Def.SortName) ->
        Map Def.SortName (SortAttributes, Set Def.SortName) ->
        Map Def.SortName (SortAttributes, Set Def.SortName)
    addSubsortInfo (super, subs) = Map.update (\(a, b) -> Just (a, b <> subs)) super

expectPresent :: (Ord k, Show k) => k -> Map k a -> a
expectPresent k =
    fromMaybe (error $ show k <> " not present in map") . Map.lookup k

{- | The state while traversing the module import graph. This is
 internal only, but the definition map contains the result of the
 traversal.
-}
data DefinitionState = State
    { moduleMap :: Map Text ParsedModule
    , definitionMap :: Map Text KoreDefinition
    , definitionAttributes :: DefinitionAttributes
    , subsorts :: Map Def.SortName (Set Def.SortName)
    }

{- | Traverses the import graph bottom up, ending in the given named
   module. All entities (sorts, symbols, axioms) that are in scope in
   that module are added to the definition map.
-}
descendFrom :: Text -> StateT DefinitionState (Except DefinitionError) ()
descendFrom m = do
    State{moduleMap, definitionMap = currentDefMap, definitionAttributes} <- get
    case Map.lookup m currentDefMap of
        Just _ -> pure () -- already internalised
        Nothing -> do
            let mbModule = Map.lookup m moduleMap
            theModule <- maybe (lift . throwE $ NoSuchModule m) pure mbModule

            -- traverse imports recursively in pre-order before
            -- dealing with the current module.
            let imported = map (Json.getId . fst) $ imports theModule
            mapM_ descendFrom imported

            -- build the module's context from imports
            defMap <- gets definitionMap
            def <-
                foldM
                    (\d1 d2 -> lift (mergeDefs d1 d2))
                    (emptyKoreDefinition definitionAttributes)
                    $ map (`expectPresent` defMap) imported

            -- validate and add new module in context of the existing
            -- definition
            (newSubsorts, newDef) <- lift $ addModule theModule def

            modify (updateState newDef newSubsorts)
  where
    updateState ::
        KoreDefinition ->
        Map Def.SortName (Set Def.SortName) ->
        DefinitionState ->
        DefinitionState
    updateState newDef newSubsorts prior =
        prior
            { definitionMap = Map.insert m newDef prior.definitionMap
            , subsorts = Map.unionWith (<>) prior.subsorts newSubsorts
            }

-- | Merges kore definitions, but collisions are forbidden (DefinitionError on collisions)
mergeDefs :: KoreDefinition -> KoreDefinition -> Except DefinitionError KoreDefinition
mergeDefs k1 k2
    | k1.attributes /= k2.attributes =
        throwE $ DefinitionAttributeError [k1.attributes, k2.attributes]
    | otherwise =
        KoreDefinition k1.attributes
            <$> mergeDisjoint modules k1 k2
            <*> mergeDisjoint sorts k1 k2
            <*> mergeDisjoint symbols k1 k2
            <*> mergeDisjoint aliases k1 k2
            <*> pure (mergeTheories k1 k2)
  where
    mergeTheories :: KoreDefinition -> KoreDefinition -> RewriteTheory
    mergeTheories m1 m2 =
        Map.unionWith (Map.unionWith (<>)) (rewriteTheory m1) (rewriteTheory m2)

    mergeDisjoint ::
        (KoreDefinition -> Map Text a) ->
        KoreDefinition ->
        KoreDefinition ->
        Except DefinitionError (Map Text a)
    mergeDisjoint selector m1 m2
        | not (null duplicates) =
            throwE $ DuplicateNames $ Set.toList duplicates
        | otherwise =
            pure $ Map.union (selector m1) (selector m2)
      where
        duplicates =
            Map.keysSet (selector m1) `Set.intersection` Map.keysSet (selector m2)

{- | Adds a module to the given definition, returning a subsort map
 and the new definition. Some validations are performed, e.g., name
 collisions are forbidden.
-}
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

            let (newSorts, sortDups) = parsedSorts `mappedBy` (.name.getId)
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
                    Map.map (\s -> (extract s, Set.singleton (s.name.getId))) newSorts
                        <> currentSorts

            -- ensure parsed symbols are not duplicates and only refer
            -- to known sorts
            let (newSymbols, symDups) = parsedSymbols `mappedBy` (.name.getId)
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
                internaliseSymbol s = do
                    info <- mkSymbolSorts sorts s
                    -- TODO(Ana): rename extract
                    pure (s.name.getId, (extract s, info))
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
                notPriority :: ParsedAlias -> Bool
                notPriority alias =
                    not $ null alias.args && "priority" `Text.isPrefixOf` alias.name.getId
            newAliases <- traverse internaliseAlias $ filter notPriority parsedAliases
            let aliases = Map.fromList newAliases <> currentAliases

            let partialDefinition = KoreDefinition{attributes, modules, sorts, symbols, aliases, rewriteTheory = currentRewriteTheory}

            (newRewriteRules, subsortPairs) <-
                partitionAxioms
                    <$> mapMaybeM (internaliseAxiom partialDefinition) parsedAxioms

            let rewriteTheory = addToTheory partialDefinition newRewriteRules currentRewriteTheory

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
internaliseRewriteRule partialDefinition aliasName aliasArgs right axAttributes sortVars = do
    alias <-
        withExcept (DefinitionAliasError aliasName) $
            Map.lookup aliasName partialDefinition.aliases
                `orFailWith` UnknownAlias aliasName
    args <- traverse (withExcept DefinitionPatternError . internaliseTerm (Just sortVars) partialDefinition) aliasArgs
    result <- expandAlias alias args
    lhs <-
        Util.retractPattern result
            `orFailWith` DefinitionTermOrPredicateError (PatternExpected result)
    rhs <-
        withExcept DefinitionPatternError $
            internalisePattern (Just sortVars) partialDefinition right
    let checkSymbolPreservesDefinedness _ SymbolAttributes{symbolType} _ = symbolType /= PartialFunction
        checkSymbolIsAc _ SymbolAttributes{isAssoc, isIdem} _ = isAssoc || isIdem
        preservesDefinedness = checkTermSymbols checkSymbolPreservesDefinedness partialDefinition rhs.term
        containsAcSymbols = checkTermSymbols checkSymbolIsAc partialDefinition lhs.term
    return RewriteRule{lhs, rhs, attributes = axAttributes, computedAttributes = ComputedAxiomAttributes{containsAcSymbols, preservesDefinedness}}

checkTermSymbols :: (Def.SymbolName -> SymbolAttributes -> SymbolSort -> Bool) -> KoreDefinition -> Def.Term -> Bool
checkTermSymbols check def = \case
    Def.AndTerm _ t1 t2 -> checkTermSymbols check def t1 && checkTermSymbols check def t2
    Def.SymbolApplication _ _ symbol ts ->
        checkSymbol symbol && foldr ((&&) . checkTermSymbols check def) True ts
    _ -> True
  where
    checkSymbol symbol = case Map.lookup symbol def.symbols of
        Just (attr, symbSort) -> check symbol attr symbSort
        Nothing -> error $ show symbol <> " symbol not found!"

expandAlias :: Alias -> [Def.Term] -> Except DefinitionError Def.TermOrPredicate
expandAlias alias currentArgs
    | length alias.args /= length currentArgs =
        throwE (DefinitionAliasError alias.name $ WrongAliasArgCount alias currentArgs)
    | otherwise =
        let substitution = Map.fromList (zip alias.args currentArgs)
         in return $ substitute substitution alias.rhs
  where
    substitute substitution termOrPredicate =
        case termOrPredicate of
            Def.APredicate predicate ->
                Def.APredicate $ Util.substituteInPredicate substitution predicate
            Def.TermAndPredicate Def.Pattern{term, constraints} ->
                Def.TermAndPredicate
                    Def.Pattern
                        { term = Util.substituteInTerm substitution term
                        , constraints =
                            Util.substituteInPredicate substitution <$> constraints
                        }

processRewriteRulesTODO :: [RewriteRule] -> [RewriteRule]
processRewriteRulesTODO = id

addToTheory :: KoreDefinition -> [RewriteRule] -> RewriteTheory -> RewriteTheory
addToTheory definition axioms theory =
    let processedRewriteRules = processRewriteRulesTODO axioms
        newTheory =
            Map.map groupByPriority
                . groupByTermIndex definition
                $ processedRewriteRules
     in Map.unionWith (Map.unionWith (<>)) theory newTheory

groupByTermIndex :: KoreDefinition -> [RewriteRule] -> Map Def.TermIndex [RewriteRule]
groupByTermIndex definition axioms =
    let withTermIndexes = do
            axiom <- axioms
            let termIndex = computeTermIndex definition axiom.lhs.term
            return (termIndex, axiom)
     in Map.fromAscList . groupSort $ withTermIndexes

groupByPriority :: [RewriteRule] -> Map Priority [RewriteRule]
groupByPriority axioms =
    Map.fromAscList . groupSort $ [(ax.attributes.priority, ax) | ax <- axioms]

{- | Checks if a given parsed symbol uses only sorts from the provided
   sort map, and whether they are consistent (wrt. sort parameter
   count), and returns a @SymbolSort@ (sort information record) for
   the symbol.
-}
mkSymbolSorts ::
    Map Def.SortName (SortAttributes, Set Def.SortName) ->
    ParsedSymbol ->
    Except DefinitionError SymbolSort
mkSymbolSorts sortMap sym =
    do
        unless (Set.size knownVars == length sym.sortVars) $
            throwE $
                DuplicateNames (map (.getId) sym.sortVars)
        resultSort <- check sym.sort
        argSorts <- mapM check sym.argSorts
        pure $ SymbolSort{resultSort, argSorts}
  where
    knownVars = Set.fromList $ map (.getId) sym.sortVars

    check :: Json.Sort -> Except DefinitionError Def.Sort
    check =
        mapExcept (first DefinitionSortError)
            . checkSort knownVars sortMap

{- | Computes all-pairs reachability in a directed graph given as an
   adjacency list mapping. Using a naive algorithm because the subsort
   graph will usually be broad and flat rather than deep.
-}
transitiveClosure :: forall k. (Ord k) => Map k (Set.Set k) -> Map k (Set.Set k)
transitiveClosure adjacencies = snd $ update adjacencies
  where
    allKeys = Map.keys adjacencies

    update :: Map k (Set.Set k) -> (Bool, Map k (Set.Set k))
    update m =
        let result@(changed, newM) = foldl' updateKey (False, m) allKeys
         in if changed then update newM else result

    -- add all children's children for a key, mark if changed
    updateKey :: (Bool, Map k (Set.Set k)) -> k -> (Bool, Map k (Set.Set k))
    updateKey (changed, m) key = (changed || thisChanged, newM)
      where
        cs = children m key
        new = cs <> foldMap (children m) cs
        newM = Map.update (Just . const new) key m
        thisChanged = cs /= new

    children :: Map k (Set.Set k) -> k -> Set.Set k
    children m k = fromMaybe Set.empty $ Map.lookup k m

----------------------------------------
data DefinitionError
    = ParseError Text
    | NoSuchModule Text
    | DuplicateSorts [ParsedSort]
    | DuplicateSymbols [ParsedSymbol]
    | DuplicateAliases [ParsedAlias]
    | DuplicateNames [Text]
    | DefinitionAttributeError [DefinitionAttributes]
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

computeTermIndex :: KoreDefinition -> Def.Term -> Def.TermIndex
computeTermIndex definition config =
    case lookForKCell config of
        Just (Def.SymbolApplication _ _ _ children) ->
            getTermIndex (lookForTopTerm (head children))
        _ -> Def.Anything
  where
    getTermIndex :: Def.Term -> Def.TermIndex
    getTermIndex term =
        case term of
            (Def.SymbolApplication _ _ symbolName _)
                | (Just (attrs, _)) <- Map.lookup symbolName definition.symbols ->
                    case attrs.symbolType of
                        Constructor -> Def.Symbol symbolName
                        _ -> Def.Anything
                | otherwise -> error "TODO: Impossible, but we need to somehow encode that the symbol exists in the definition"
            _ -> Def.Anything

    -- it is assumed there is only one K cell
    lookForKCell :: Def.Term -> Maybe Def.Term
    lookForKCell =
        \case
            kCell@(Def.SymbolApplication _ _ symbolName children)
                | symbolName == "Lbl'-LT-'k'-GT-'" ->
                    Just kCell
                | otherwise ->
                    asum $ lookForKCell <$> children
            Def.AndTerm _ t1 t2 ->
                lookForKCell t1 <|> lookForKCell t2
            Def.DomainValue _ _ -> Nothing
            Def.Var _ -> Nothing

    -- this assumes that the top kseq is already normalized into right-assoc form
    lookForTopTerm :: Def.Term -> Def.Term
    lookForTopTerm =
        \case
            Def.SymbolApplication _ _ symbolName children
                | symbolName == "kseq" ->
                    let firstChild = getKSeqFirst children
                     in stripAwaySortInjections firstChild
                | otherwise ->
                    error ("lookForTopTerm: the first child of the K cell isn't a kseq" <> show symbolName)
            term -> term

    -- this assumes that sort injections are well-formed (have a single argument)
    stripAwaySortInjections :: Def.Term -> Def.Term
    stripAwaySortInjections =
        \case
            term@(Def.SymbolApplication _ _ symbolName children)
                | symbolName == "inj" ->
                    stripAwaySortInjections (getInjChild children)
                | otherwise -> term
            term -> term

    getKSeqFirst [] = error "lookForTopTerm: empty KSeq"
    getKSeqFirst (x : _) = x

    getInjChild [] = error "stripAwaySortInjections: injection with 0 children"
    getInjChild [x] = x
    getInjChild _ = error "stripAwaySortInjections: injection with multiple children"