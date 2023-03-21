{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Converts a @ParsedDefinition@ to a @KoreDefinition@, extracting all
data needed internally from the parsed entities.
-}
module Booster.Syntax.ParsedKore.Internalise (
    buildDefinitions,
    addToDefinitions,
    lookupModule,
    DefinitionError (..),
) where

import Control.Monad
import Control.Monad.Extra (mapMaybeM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Aeson (ToJSON (..), Value (..), object, (.=))
import Data.Bifunctor (first, second)
import Data.ByteString.Char8 (ByteString)
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
import Data.Text.Encoding qualified as Text
import Data.Tuple (swap)
import Prettyprinter

import Booster.Definition.Attributes.Base
import Booster.Definition.Attributes.Reader
import Booster.Definition.Base as Def
import Booster.Pattern.Base qualified as Def
import Booster.Pattern.Index (TermIndex, computeTermIndex)
import Booster.Pattern.Util qualified as Util
import Booster.Prettyprinter hiding (attributes)
import Booster.Syntax.Json.Base qualified as Json
import Booster.Syntax.Json.Internalise
import Booster.Syntax.ParsedKore.Base

{- | Traverses all modules of a parsed definition, to build internal
@KoreDefinition@s for each of the modules (when used as the main
module). The returned mapping can be retained to switch main module
for RPC requests.

Only very few validations are performed on the parsed data.
-}
buildDefinitions :: ParsedDefinition -> Except DefinitionError (Map Text KoreDefinition)
buildDefinitions def@ParsedDefinition{modules} = do
    definitionMap <$> execStateT buildAllModules startState
  where
    moduleMap = Map.fromList [(m.name.getId, m) | m <- modules]
    startState =
        State
            { moduleMap
            , definitionMap = Map.empty
            , definitionAttributes = extract def
            }
    buildAllModules = mapM descendFrom $ Map.keys moduleMap

{- | API function that adds the KoreDefinition for a given new module to
   the map of KoreDefinitions per main module.

It takes a map of already-known modules and the 'KoreDefinition's that
they have in scope, and a new module (that is not one of the existing
ones), computes the 'KoreDefinition' of that module as the main
module, and adds it to the map.
-}
addToDefinitions ::
    ParsedModule ->
    Map Text KoreDefinition ->
    Except DefinitionError (Map Text KoreDefinition)
addToDefinitions m prior
    | Map.member m.name.getId prior =
        throwE $ DuplicateModule m.name.getId
    | otherwise = do
        definitionMap <$> execStateT (descendFrom m.name.getId) currentState
  where
    currentState =
        State
            { moduleMap = Map.singleton m.name.getId m
            , definitionMap = prior
            , definitionAttributes = DefinitionAttributes
            }

lookupModule :: Text -> Map Text a -> Except DefinitionError a
lookupModule k =
    maybe (throwE $ NoSuchModule k) pure . Map.lookup k

{- | The state while traversing the module import graph. The definition
 map contains internalisations of all modules that were touched in the
 traversal.
-}
data DefinitionState = State
    { moduleMap :: Map Text ParsedModule
    , definitionMap :: Map Text KoreDefinition
    , definitionAttributes :: DefinitionAttributes
    }

-- Helper types to signal incomplete definitions
newtype ImportedDefinition = Imported {imported :: KoreDefinition}

newtype PartialDefinition = Partial {partial :: KoreDefinition}

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
                    ( \def modName -> do
                        modu <- lift $ lookupModule modName defMap
                        lift (mergeDefs def modu)
                    )
                    (Imported $ emptyKoreDefinition definitionAttributes)
                    imported

            -- validate and add new module in context of the existing
            -- definition
            newDef <- lift $ addModule theModule def

            modify (\s -> s{definitionMap = Map.insert m newDef s.definitionMap})

-- | Merges kore definitions, but collisions are forbidden (DefinitionError on collisions)
mergeDefs :: ImportedDefinition -> KoreDefinition -> Except DefinitionError ImportedDefinition
mergeDefs k1 k2
    | k1.imported.attributes /= k2.attributes =
        throwE $ DefinitionAttributeError [k1.imported.attributes, k2.attributes]
    | otherwise =
        fmap Imported $
            KoreDefinition k2.attributes
                <$> mergeDisjoint modules k1 k2
                <*> mergeDisjoint sorts k1 k2
                <*> mergeDisjoint symbols k1 k2
                <*> mergeDisjoint aliases k1 k2
                <*> pure (mergeTheories k1 k2)
  where
    mergeTheories :: ImportedDefinition -> KoreDefinition -> RewriteTheory
    mergeTheories (Imported m1) m2 =
        Map.unionWith (Map.unionWith (<>)) (rewriteTheory m1) (rewriteTheory m2)

    mergeDisjoint ::
        (KoreDefinition -> Map ByteString a) ->
        ImportedDefinition ->
        KoreDefinition ->
        Except DefinitionError (Map ByteString a)
    mergeDisjoint selector (Imported m1) m2
        | not (null duplicates) =
            throwE $ DuplicateNames $ map Text.decodeLatin1 $ Set.toList duplicates
        | otherwise =
            pure $ Map.union (selector m1) (selector m2)
      where
        duplicates =
            Map.keysSet (selector m1) `Set.intersection` Map.keysSet (selector m2)

{- | Internal helper which adds the contents of a local module to the
   imported 'KoreDefinition'. Given a 'ParsedModule' and a 'KoreDefinition'
   of entities that are in scope via imports, it adds the sorts,
   aliases, and rules of the module to the 'KoreDefinition'.

Some validations are performed, e.g., name collisions are forbidden.
-}
addModule ::
    ParsedModule ->
    ImportedDefinition ->
    Except DefinitionError KoreDefinition
addModule
    m@ParsedModule
        { name = Json.Id n
        , sorts = parsedSorts
        , symbols = parsedSymbols
        , aliases = parsedAliases
        , axioms = parsedAxioms
        }
    ( Imported
            ( KoreDefinition
                    { attributes
                    , modules = currentModules
                    , sorts = currentSorts
                    , symbols = currentSymbols
                    , aliases = currentAliases
                    , rewriteTheory = currentRewriteTheory
                    }
                )
        ) =
        do
            --
            let modName = textToBS n
            when (modName `Map.member` currentModules) $
                throwE $
                    DuplicateModule n
            let modules = Map.insert modName (extract m) currentModules

            -- ensure sorts are unique and only refer to known other sorts
            let (newSorts, sortDups) = parsedSorts `mappedBy` (textToBS . (.name.getId))
            unless (null sortDups) $
                throwE $
                    DuplicateSorts (concatMap snd sortDups)
            let sortCollisions :: [ParsedSort]
                sortCollisions =
                    Map.elems $ Map.intersection newSorts currentSorts
            unless (null sortCollisions) $
                throwE $
                    DuplicateSorts sortCollisions
            -- prior and locally-defined sorts, no subsort information
            let sorts' =
                    Map.map (\s -> (extract s, Set.singleton (textToBS s.name.getId))) newSorts
                        <> currentSorts

            -- ensure parsed symbols are not duplicates and only refer
            -- to known sorts
            let (newSymbols, symDups) = parsedSymbols `mappedBy` (textToBS . (.name.getId))
                symCollisions =
                    Map.elems $ Map.intersection newSymbols currentSymbols
            unless (null symDups) $
                throwE $
                    DuplicateSymbols (concatMap snd symDups)
            unless (null symCollisions) $
                throwE $
                    DuplicateSymbols symCollisions
            newSymbols' <- traverse (internaliseSymbol sorts') parsedSymbols
            let symbols = Map.fromList newSymbols' <> currentSymbols

            let defWithNewSortsAndSymbols =
                    Partial
                        KoreDefinition
                            { attributes
                            , modules
                            , sorts = sorts' -- no subsort information yet
                            , symbols
                            , aliases = currentAliases -- no aliases yet
                            , rewriteTheory = currentRewriteTheory -- no rules yet
                            }

            let internaliseAlias ::
                    ParsedAlias ->
                    Except DefinitionError (Def.AliasName, Alias)
                -- TODO(Ana): do we need to handle attributes?
                internaliseAlias palias@ParsedAlias{name, sortVars, argSorts, sort, args, rhs} = do
                    unless (length argSorts == length args) (throwE (DefinitionAliasError (Json.getId name) . WrongAliasSortCount $ palias))
                    let paramNames = Json.getId <$> sortVars
                        params = Def.SortVar . textToBS <$> paramNames
                        argNames = textToBS . Json.getId <$> args
                        internalName = textToBS $ Json.getId name
                    internalArgSorts <- traverse (withExcept DefinitionSortError . checkSort (Set.fromList paramNames) sorts') argSorts
                    internalResSort <- withExcept DefinitionSortError $ checkSort (Set.fromList paramNames) sorts' sort
                    let internalArgs = uncurry Def.Variable <$> zip internalArgSorts argNames
                    internalRhs <-
                        withExcept (DefinitionAliasError (Json.getId name) . InconsistentAliasPattern) $
                            internaliseTermOrPredicate (Just sortVars) defWithNewSortsAndSymbols.partial rhs
                    let rhsSort = Util.sortOfTermOrPredicate internalRhs
                    unless (fromMaybe internalResSort rhsSort == internalResSort) (throwE (DefinitionSortError (GeneralError "IncompatibleSorts")))
                    return (internalName, Alias{name = internalName, params, args = internalArgs, rhs = internalRhs})
                -- filter out "antiLeft" aliases, recognised by name and argument count
                notPriority :: ParsedAlias -> Bool
                notPriority alias =
                    not $ null alias.args && "priority" `Text.isPrefixOf` alias.name.getId
            newAliases <- traverse internaliseAlias $ filter notPriority parsedAliases
            let aliases = Map.fromList newAliases <> currentAliases

            let defWithAliases :: PartialDefinition
                defWithAliases = Partial defWithNewSortsAndSymbols.partial{aliases}

            (newRewriteRules, subsortPairs) <-
                partitionAxioms
                    <$> mapMaybeM (internaliseAxiom defWithAliases) parsedAxioms

            let rewriteTheory = addToTheory newRewriteRules currentRewriteTheory
                sorts = subsortClosure sorts' subsortPairs

            pure $ defWithAliases.partial{sorts, rewriteTheory}
      where
        -- Uses 'getKey' to construct a finite mapping from the list,
        -- returning elements that yield the same key separately.
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

        subsortClosure ::
            Map Def.SortName (SortAttributes, Set Def.SortName) ->
            [(Def.SortName, Def.SortName)] ->
            Map Def.SortName (SortAttributes, Set Def.SortName)
        subsortClosure priorSortMap subsortPairs =
            Map.intersectionWith (,) attributeMap newSubsortMap
          where
            attributeMap = Map.map fst priorSortMap
            newSubsortMap =
                transitiveClosure $ Map.unionWith (<>) (Map.map snd priorSortMap) newSubsorts
            newSubsorts =
                Map.fromListWith (<>) $ map (second Set.singleton . swap) subsortPairs

-- Result type from internalisation of different axioms
data AxiomResult
    = -- | Rewrite rule
      RewriteRuleAxiom RewriteRule
    | -- | subsort data: a pair of sorts
      SubsortAxiom (Def.SortName, Def.SortName)

-- helper type to carry relevant extracted data from a pattern (what
-- is passed to the internalising function later)
data AxiomData
    = RewriteRuleAxiom' Text [Json.KorePattern] Json.KorePattern AxiomAttributes [Json.Id]
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
        | Json.KJEquals{first = aVar, second = anApp} <- arg
        , aVar == Json.KJEVar{name = var, sort = super}
        , Json.KJApp{name, args} <- anApp
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
    PartialDefinition ->
    ParsedAxiom ->
    Except DefinitionError (Maybe AxiomResult)
internaliseAxiom (Partial partialDefinition) parsedAxiom =
    classifyAxiom parsedAxiom >>= maybe (pure Nothing) processAxiom
  where
    processAxiom :: AxiomData -> Except DefinitionError (Maybe AxiomResult)
    processAxiom = \case
        SubsortAxiom' Json.SortApp{name = Json.Id sub} Json.SortApp{name = Json.Id super} -> do
            when (sub == super) $
                throwE $
                    DefinitionSortError $
                        GeneralError ("Bad subsort rule " <> sub <> " < " <> super)
            pure $ Just $ SubsortAxiom (textToBS sub, textToBS super)
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
                <$> internaliseRewriteRule partialDefinition (textToBS alias) args rhs attribs sortVars

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
        withExcept (DefinitionAliasError $ Text.decodeLatin1 aliasName) $
            Map.lookup aliasName partialDefinition.aliases
                `orFailWith` UnknownAlias aliasName
    args <- traverse (withExcept DefinitionPatternError . internaliseTerm (Just sortVars) partialDefinition) aliasArgs
    result <- expandAlias alias args

    -- prefix all variables in lhs and rhs with "Rule#" to avoid
    -- name clashes with patterns from the user
    -- filter out literal `Top` constraints
    lhs <-
        fmap (removeTops . Util.modifyVariables ("Rule#" <>)) $
            Util.retractPattern result
                `orFailWith` DefinitionTermOrPredicateError (PatternExpected result)
    rhs <-
        fmap (removeTops . Util.modifyVariables ("Rule#" <>)) $
            withExcept DefinitionPatternError $
                internalisePattern (Just sortVars) partialDefinition right
    let preservesDefinedness =
            -- users can override the definedness computation by an explicit attribute
            fromMaybe (Util.checkTermSymbols Util.isDefinedSymbol rhs.term) axAttributes.preserving
        containsAcSymbols =
            Util.checkTermSymbols Util.checkSymbolIsAc lhs.term
        computedAttributes =
            ComputedAxiomAttributes{preservesDefinedness, containsAcSymbols}
    return RewriteRule{lhs, rhs, attributes = axAttributes, computedAttributes}
  where
    removeTops :: Def.Pattern -> Def.Pattern
    removeTops p = p{Def.constraints = filter (/= Def.Top) p.constraints}

expandAlias :: Alias -> [Def.Term] -> Except DefinitionError Def.TermOrPredicate
expandAlias alias currentArgs
    | length alias.args /= length currentArgs =
        throwE (DefinitionAliasError (Text.decodeLatin1 alias.name) $ WrongAliasArgCount alias currentArgs)
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

addToTheory :: [RewriteRule] -> RewriteTheory -> RewriteTheory
addToTheory axioms theory =
    let newTheory =
            Map.map groupByPriority
                . groupByTermIndex
                $ axioms
     in Map.unionWith (Map.unionWith (<>)) theory newTheory

groupByTermIndex :: [RewriteRule] -> Map TermIndex [RewriteRule]
groupByTermIndex axioms =
    let withTermIndexes = do
            axiom <- axioms
            let termIndex = computeTermIndex axiom.lhs.term
            return (termIndex, axiom)
     in Map.fromAscList . groupSort $ withTermIndexes

groupByPriority :: [RewriteRule] -> Map Priority [RewriteRule]
groupByPriority axioms =
    Map.fromAscList . groupSort $ [(ax.attributes.priority, ax) | ax <- axioms]

internaliseSymbol ::
    Map Def.SortName (SortAttributes, Set Def.SortName) ->
    ParsedSymbol ->
    Except DefinitionError (Def.SymbolName, Def.Symbol)
internaliseSymbol sorts parsedSymbol = do
    unless (Set.size knownVars == length parsedSymbol.sortVars) $
        throwE $
            DuplicateNames (map (.getId) parsedSymbol.sortVars)
    resultSort <- check parsedSymbol.sort
    argSorts <- mapM check parsedSymbol.argSorts
    let name = textToBS parsedSymbol.name.getId
        attributes = extract parsedSymbol
        internalSymbol = Def.Symbol{name, sortVars, resultSort, argSorts, attributes}
    -- TODO(Ana): rename extract
    pure (name, internalSymbol)
  where
    knownVars = Set.fromList sortVarsT
    sortVarsT = map (.getId) parsedSymbol.sortVars
    sortVars = map textToBS sortVarsT

    check :: Json.Sort -> Except DefinitionError Def.Sort
    check =
        mapExcept (first DefinitionSortError)
            . checkSort knownVars sorts

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
    | DuplicateModule Text
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
    | AddModuleError Text
    deriving stock (Eq, Show)

instance Pretty DefinitionError where
    pretty = \case
        ParseError msg ->
            "Parse error: " <> pretty msg
        NoSuchModule name ->
            pretty $ name <> ": No such module"
        DuplicateModule name ->
            pretty $ name <> ": Duplicate module"
        DuplicateSorts sorts ->
            pretty $ "Duplicate sorts: " <> show (map (.name.getId) sorts)
        DuplicateSymbols syms ->
            pretty $ "Duplicate symbols: " <> show (map (.name.getId) syms)
        DuplicateAliases aliases ->
            pretty $ "Duplicate aliases: " <> show (map (.name.getId) aliases)
        DuplicateNames names ->
            pretty $ "Duplicate names (import clashes): " <> show names
        DefinitionAttributeError attrs ->
            pretty $ "Definition attributes differ: " <> show attrs
        DefinitionSortError sortErr ->
            pretty $ "Sort error: " <> renderSortError sortErr
        DefinitionPatternError patErr ->
            pretty $ "Pattern error: " <> show patErr -- TODO define a pretty instance?
        DefinitionAliasError name err ->
            pretty $ "Alias error in " <> Text.unpack name <> ": " <> show err
        DefinitionRewriteRuleError (MalformedRewriteRule rule) ->
            pretty $ "Malformed rewrite rule " <> show (extract rule).location
        DefinitionTermOrPredicateError (PatternExpected p) ->
            pretty $ "Expected a pattern but found a predicate: " <> show p
        AddModuleError msg ->
            pretty $ "Add-module error: " <> msg

{- | ToJSON instance (user-facing for add-module endpoint):
Renders the error string as 'error', with minimal context.
-}
instance ToJSON DefinitionError where
    toJSON = \case
        DuplicateSorts sorts ->
            "Duplicate sorts" `withContext` map toJSON sorts
        DuplicateSymbols syms ->
            "Duplicate symbols" `withContext` map toJSON syms
        DuplicateAliases aliases ->
            "DuplicateAliases" `withContext` map toJSON aliases
        DefinitionPatternError patErr ->
            "Pattern error in definition" `withContext` [toJSON patErr]
        DefinitionRewriteRuleError (MalformedRewriteRule rule) ->
            "Malformed rewrite rule" `withContext` [toJSON rule]
        other ->
            object ["error" .= renderOneLineText (pretty other), "context" .= Null]
      where
        withContext :: Text -> [Value] -> Value
        withContext errMsg context =
            object ["error" .= errMsg, "context" .= context]

data AliasError
    = UnknownAlias AliasName
    | WrongAliasSortCount ParsedAlias
    | WrongAliasArgCount Alias [Def.Term]
    | InconsistentAliasPattern [PatternError]
    deriving stock (Eq, Show)

newtype RewriteRuleError
    = MalformedRewriteRule ParsedAxiom
    deriving stock (Eq, Show)

newtype TermOrPredicateError
    = PatternExpected Def.TermOrPredicate
    deriving stock (Eq, Show)
