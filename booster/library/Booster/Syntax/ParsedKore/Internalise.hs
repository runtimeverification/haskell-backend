{-# LANGUAGE FlexibleContexts #-}
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
import Data.Coerce (coerce)
import Data.Function (on)
import Data.List (foldl', groupBy, nub, partition, sortOn)
import Data.List.Extra (groupSort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Tuple (swap)
import GHC.Records (HasField (..))
import Prettyprinter as Pretty

import Booster.Definition.Attributes.Base
import Booster.Definition.Attributes.Reader as Attributes (
    HasAttributes (mkAttributes),
    readLocation,
 )
import Booster.Definition.Base as Def
import Booster.Definition.Util (HasSourceRef (..), SourceRef)
import Booster.Pattern.Base (Variable (..))
import Booster.Pattern.Base qualified as Def
import Booster.Pattern.Base qualified as Def.Symbol (Symbol (..))

import Booster.Definition.Attributes.Base qualified as Def
import Booster.Pattern.Index as Idx
import Booster.Pattern.Util qualified as Util
import Booster.Prettyprinter hiding (attributes)
import Booster.Syntax.Json.Internalise
import Booster.Syntax.ParsedKore.Base
import Kore.Syntax.Json.Types (Id, Sort)
import Kore.Syntax.Json.Types qualified as Syntax

{- | Traverses all modules of a parsed definition, to build internal
@KoreDefinition@s for each of the modules (when used as the main
module). The returned mapping can be retained to switch main module
for RPC requests.

Only very few validations are performed on the parsed data.
-}
buildDefinitions :: ParsedDefinition -> Except DefinitionError (Map Text KoreDefinition)
buildDefinitions def@ParsedDefinition{modules} = do
    definitionAttributes <- withExcept DefinitionAttributeError $ mkAttributes def
    definitionMap
        <$> execStateT
            buildAllModules
            State{moduleMap, definitionMap = Map.empty, definitionAttributes}
  where
    moduleMap = Map.fromList [(m.name.getId, m) | m <- modules]
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
            let imported = map ((.getId) . fst) $ imports theModule
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
        throwE $
            DefinitionAttributeError $
                "Definition attributes differ: " <> Text.pack (show [k1.imported.attributes, k2.attributes])
    | otherwise =
        fmap Imported $
            KoreDefinition k2.attributes
                <$> mergeDisjoint modules k1 k2
                <*> mergeDisjoint sorts k1 k2
                <*> mergeDisjoint symbols k1 k2
                <*> mergeDisjoint aliases k1 k2
                <*> pure (mergeTheories rewriteTheory k1 k2)
                <*> pure (mergeTheories functionEquations k1 k2)
                <*> pure (mergeTheories simplifications k1 k2)
                <*> pure (mergeTheories predicateSimplifications k1 k2)
  where
    mergeTheories ::
        forall r.
        (KoreDefinition -> Theory r) ->
        ImportedDefinition ->
        KoreDefinition ->
        Theory r
    mergeTheories selector (Imported m1) m2 =
        Map.unionWith (Map.unionWith (<>)) (selector m1) (selector m2)

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
        { name = Syntax.Id n
        , sorts = parsedSorts
        , symbols = parsedSymbols
        , aliases = parsedAliases
        , axioms = parsedAxioms
        }
    ( Imported
            ( KoreDefinition
                    { attributes = defAttributes
                    , modules = currentModules
                    , sorts = currentSorts
                    , symbols = currentSymbols
                    , aliases = currentAliases
                    , rewriteTheory = currentRewriteTheory
                    , functionEquations = currentFctEqs
                    , simplifications = currentSimpls
                    , predicateSimplifications = currentPredicateSimplifications
                    }
                )
        ) =
        do
            --
            let modName = textToBS n
            when (modName `Map.member` currentModules) $
                throwE $
                    DuplicateModule n
            attributes <- withExcept DefinitionAttributeError $ mkAttributes m
            let modules = Map.insert modName attributes currentModules

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
            let mkSortEntry ::
                    ParsedSort -> Except DefinitionError (SortAttributes, Set ByteString)
                mkSortEntry parsedSort =
                    withExcept DefinitionAttributeError $
                        (,Set.singleton (textToBS parsedSort.name.getId))
                            <$> mkAttributes parsedSort
            newSorts' <- traverse mkSortEntry newSorts

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
            let sorts' = currentSorts <> newSorts'
            newSymbols' <- traverse (internaliseSymbol sorts') parsedSymbols
            symbols <- (<> currentSymbols) <$> addKmapSymbols newSorts' (Map.fromList newSymbols')

            let defWithNewSortsAndSymbols =
                    Partial
                        KoreDefinition
                            { attributes = defAttributes
                            , modules
                            , sorts = sorts' -- no subsort information yet
                            , symbols
                            , aliases = currentAliases -- no aliases yet
                            , rewriteTheory = currentRewriteTheory -- no rules yet
                            , functionEquations = Map.empty
                            , simplifications = Map.empty
                            , predicateSimplifications = Map.empty
                            }

            let internaliseAlias ::
                    ParsedAlias ->
                    Except DefinitionError (Def.AliasName, Alias)
                -- TODO(Ana): do we need to handle attributes?
                internaliseAlias palias@ParsedAlias{name, sortVars, argSorts, sort, args, rhs} = do
                    unless
                        (length argSorts == length args)
                        (throwE (DefinitionAliasError name.getId . WrongAliasSortCount $ palias))
                    let paramNames = (.getId) <$> sortVars
                        params = Def.SortVar . textToBS <$> paramNames
                        argNames = textToBS . (.getId) <$> args
                        internalName = textToBS name.getId
                    internalArgSorts <-
                        traverse
                            (withExcept DefinitionSortError . internaliseSort (Set.fromList paramNames) sorts')
                            argSorts
                    internalResSort <-
                        withExcept DefinitionSortError $
                            internaliseSort (Set.fromList paramNames) sorts' sort
                    let internalArgs = uncurry Def.Variable <$> zip internalArgSorts argNames
                    internalRhs <-
                        withExcept (DefinitionAliasError name.getId . InconsistentAliasPattern) $
                            internaliseTermOrPredicate True (Just sortVars) defWithNewSortsAndSymbols.partial rhs
                    let rhsSort = Util.sortOfTermOrPredicate internalRhs
                    unless
                        (fromMaybe internalResSort rhsSort == internalResSort)
                        (throwE (DefinitionSortError (GeneralError "IncompatibleSorts")))
                    return (internalName, Alias{name = internalName, params, args = internalArgs, rhs = internalRhs})
                -- filter out "antiLeft" aliases, recognised by name and argument count
                notPriority :: ParsedAlias -> Bool
                notPriority alias =
                    not $ null alias.args && "priority" `Text.isPrefixOf` alias.name.getId
            newAliases <- traverse internaliseAlias $ filter notPriority parsedAliases
            let aliases = Map.fromList newAliases <> currentAliases

            let defWithAliases :: PartialDefinition
                defWithAliases = Partial defWithNewSortsAndSymbols.partial{aliases}
            newAxioms <- mapMaybeM (internaliseAxiom defWithAliases) parsedAxioms

            let newRewriteRules = mapMaybe retractRewriteRule newAxioms
                subsortPairs = mapMaybe retractSubsortRule newAxioms
                newFunctionEquations = mapMaybe retractFunctionRule newAxioms
                newSimplifications = mapMaybe retractSimplificationRule newAxioms
                newPredicateSimplifications = mapMaybe retractPredicateSimplificationRule newAxioms
            let rewriteTheory =
                    addToTheoryWith (Idx.kCellTermIndex . (.lhs)) newRewriteRules currentRewriteTheory
                functionEquations =
                    addToTheoryWith (Idx.termTopIndex . (.lhs)) newFunctionEquations currentFctEqs
                simplifications =
                    addToTheoryWith (Idx.termTopIndex . (.lhs)) newSimplifications currentSimpls
                sorts = subsortClosure sorts' subsortPairs
                predicateSimplifications =
                    addToTheoryWith
                        (predicateTopIndex . (.target))
                        newPredicateSimplifications
                        currentPredicateSimplifications

            pure $
                defWithAliases.partial
                    { sorts
                    , rewriteTheory
                    , functionEquations
                    , simplifications
                    , predicateSimplifications
                    }
      where
        -- Uses 'getKey' to construct a finite mapping from the list,
        -- returning elements that yield the same key separately.
        mappedBy ::
            forall a k.
            Ord k =>
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

        addKmapSymbols ::
            Map Def.SortName (SortAttributes, Set Def.SortName) ->
            Map Def.SymbolName Def.Symbol ->
            Except DefinitionError (Map Def.SymbolName Def.Symbol)
        addKmapSymbols sorts symbols = do
            let
                extractKeyElemSortName :: Def.SymbolName -> Except DefinitionError (Def.SortName, Def.SortName)
                extractKeyElemSortName symbolName = case Map.lookup symbolName symbols of
                    Just Def.Symbol{argSorts = [Def.SortApp keySortName [], Def.SortApp elemSortName []]} -> pure (keySortName, elemSortName)
                    Just s -> throwE $ ElemSymbolMalformed s
                    Nothing -> throwE $ ElemSymbolNotFound symbolName

            -- extractedMapSymbolNames :: Map Def.SymbolName Def.KMapDefinition
            extractedMapSymbolNames <-
                foldM
                    ( \rest (mapSortName, (SortAttributes{kmapAttributes}, _)) -> case kmapAttributes of
                        Just symbolNames@KMapAttributes{unitSymbolName, elementSymbolName, concatSymbolName} -> do
                            (keySortName, elementSortName) <- extractKeyElemSortName elementSymbolName
                            let def = KMapDefinition{symbolNames, mapSortName, keySortName, elementSortName}
                            pure $
                                Map.fromList [(unitSymbolName, def), (elementSymbolName, def), (concatSymbolName, def)]
                                    `Map.union` rest
                        _ -> pure rest
                    )
                    mempty
                    (Map.toList sorts)
            pure $
                Map.mapWithKey
                    ( \symbolName sym@Def.Symbol{attributes} -> case Map.lookup symbolName extractedMapSymbolNames of
                        Just def ->
                            sym{Def.Symbol.attributes = attributes{Def.isKMapSymbol = Just def}}
                        Nothing -> sym
                    )
                    symbols

-- Result type from internalisation of different axioms
data AxiomResult
    = -- | Rewrite rule
      RewriteRuleAxiom (RewriteRule "Rewrite")
    | -- | subsort data: a pair of sorts
      SubsortAxiom (Def.SortName, Def.SortName)
    | -- | Function equation
      FunctionAxiom (RewriteRule "Function")
    | -- | Simplification
      SimplificationAxiom (RewriteRule "Simplification")
    | -- | Predicate simplification
      PredicateSimplificationAxiom PredicateEquation

-- retract helpers
retractRewriteRule :: AxiomResult -> Maybe (RewriteRule "Rewrite")
retractRewriteRule (RewriteRuleAxiom r) = Just r
retractRewriteRule _ = Nothing

retractSubsortRule :: AxiomResult -> Maybe (Def.SortName, Def.SortName)
retractSubsortRule (SubsortAxiom r) = Just r
retractSubsortRule _ = Nothing

retractFunctionRule :: AxiomResult -> Maybe (RewriteRule "Function")
retractFunctionRule (FunctionAxiom r) = Just r
retractFunctionRule _ = Nothing

retractSimplificationRule :: AxiomResult -> Maybe (RewriteRule "Simplification")
retractSimplificationRule (SimplificationAxiom r) = Just r
retractSimplificationRule _ = Nothing

retractPredicateSimplificationRule :: AxiomResult -> Maybe PredicateEquation
retractPredicateSimplificationRule (PredicateSimplificationAxiom r) = Just r
retractPredicateSimplificationRule _ = Nothing

-- helper type to carry relevant extracted data from a pattern (what
-- is passed to the internalising function later)
data AxiomData
    = RewriteRuleAxiom' Text [Syntax.KorePattern] Syntax.KorePattern AxiomAttributes
    | RewriteRuleAxiomNoAlias' Syntax.KorePattern Syntax.KorePattern AxiomAttributes
    | SubsortAxiom' Syntax.Sort Syntax.Sort
    | FunctionAxiom'
        Syntax.KorePattern -- requires
        [(Syntax.Id, Syntax.Sort, Syntax.KorePattern)] -- arguments (as variable substitution)
        Syntax.KorePattern -- LHS
        Syntax.KorePattern -- And(RHS, ensures)
        [Syntax.Id] -- sort variables
        AxiomAttributes
    | SimplificationAxiom'
        Syntax.KorePattern -- requires
        Syntax.KorePattern -- LHS
        Syntax.KorePattern -- And(RHS, ensures)
        [Syntax.Id] -- sort variables
        AxiomAttributes

{- | Recognises axioms generated from a K definition and classifies them
   according to their purpose.

* Rewrite rule:
  - with anti-left and alias:    \rewrites(\and{}(\not(_), <aliasName>(..)), _)
  - without anti-left, but alias: \rewrites(<aliasName>(..)), _)
  - simple format: (lhs positions flexible but \and mandatory)
    \rewrites(\and(<lhs>, <reqs>), rhs) or \rewrites(\and(<reqs>, <lhs>), <rhs>)
* Subsort axiom:
  \exists(V:<super>, \equals(V, inj{<sub>,<super>}(V':<sub>)))
* equation (simplification or function equation)
  \implies(<requires>, \equals(<lhs-symbol>(_), \and(<rhs>, <ensures>)))
* matching logic simplification equation
  \implies(<requires>, \equals(lhs, \and(<rhs>, <ensures>)))
  (with lhs something different from a symbol application). Used in
  domains.md for SortBool simplification
* functional/total rule
  \exists(V:_ , \equals(V, <total-symbol>(..args..))) [functional()]
* no confusion, same constructor (con)
  \implies(\and(<con>(X), <con>(Y)), <con>(\and(X, Y))) [constructor()]
* no confusion, different constructors (con1, con2)
  \not(\and(<con1>(X), <con2>(Y))) [constructor()]
* no junk: chain of \or (possibly with chain of \exists in arguments) ending in \bottom
  \or(\exists(X, \exists(Y, ..., <con>(X, Y, ...)), \or(..., \bottom)) [constructor()]
* associativity
  \equals(<sym>(<sym>(K1, K2), K3), <sym>(K1, <sym>(K2, K3))) [assoc()]
* commutativity
  \equals(<sym>(K1, K2), <sym>(K2, K1)) [comm()]
* idempotency
  \equals(<sym>(K, K), K) [idem()]
* left unit
  \equals(<sym1>(<unit>, K), K) [unit()]
* right unit
  \equals(<sym1>(K, <unit>), K) [unit()]

* one bespoke simplification rule for injections:
  '\equals{...}(inj{S2, S3}(inj{S1, S2}(T:S1), inj{S1, S3}(T:S1))'
  without conditions (no \implies)
* some no-junk axioms are just "\bottom{...}" (SortList, SortK, SortMap, SortSet)
-}
classifyAxiom :: ParsedAxiom -> Except DefinitionError (Maybe AxiomData)
classifyAxiom parsedAx@ParsedAxiom{axiom, sortVars, attributes} =
    case axiom of
        -- rewrite: an actual rewrite rule
        Syntax.KJRewrites _ lhs rhs
            | Syntax.KJAnd _ (Syntax.KJNot _ _) (Syntax.KJApp (Syntax.Id aliasName) _ aliasArgs) <- lhs ->
                Just . RewriteRuleAxiom' aliasName aliasArgs rhs
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            | Syntax.KJApp (Syntax.Id aliasName) _ aliasArgs <- lhs ->
                Just . RewriteRuleAxiom' aliasName aliasArgs rhs
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            | Syntax.KJAnd{} <- lhs ->
                Just . RewriteRuleAxiomNoAlias' lhs rhs
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            | otherwise ->
                throwE $ DefinitionAxiomError $ MalformedRewriteRule parsedAx
        -- subsort axiom formulated as an existential rule
        Syntax.KJExists{var, varSort = super, arg}
            | Syntax.KJEquals{first = aVar, second = anApp} <- arg
            , aVar == Syntax.KJEVar{name = var, sort = super}
            , Syntax.KJApp{name, args} <- anApp
            , Syntax.Id "inj" <- name
            , [Syntax.KJEVar{name = _, sort = sub}] <- args ->
                pure $ Just $ SubsortAxiom' sub super
        -- implies with a symbol application: an equation
        Syntax.KJImplies _ req (Syntax.KJEquals _ _ lhs@Syntax.KJApp{args} rhs@Syntax.KJAnd{})
            | hasAttribute "simplification" ->
                Just . SimplificationAxiom' req lhs rhs sortVars
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            -- requires and argument predicate, no antiLeft
            | Syntax.KJAnd _ requires argPred@Syntax.KJAnd{first = Syntax.KJIn{}} <- req
            , all isVar args -> do
                argTuples <- extractBinders argPred
                Just . FunctionAxiom' requires argTuples lhs rhs sortVars
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            -- antiLeft (discarded), requires and argument predicate
            | Syntax.KJAnd _ _antiLeft Syntax.KJAnd{first = reqs, second = argPred} <- req
            , all isVar args -> do
                argTuples <- extractBinders argPred
                Just . FunctionAxiom' reqs argTuples lhs rhs sortVars
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            -- no arguments, no antiLeft
            | Syntax.KJAnd _ requires Syntax.KJTop{} <- req
            , all isVar args -> do
                Just . FunctionAxiom' requires [] lhs rhs sortVars
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
            | otherwise ->
                throwE $ DefinitionAxiomError $ MalformedEquation parsedAx
        -- implies with the LHS not a symbol application, tagged as simplification
        Syntax.KJImplies _ req (Syntax.KJEquals _sort _ lhs rhs@Syntax.KJAnd{})
            | hasAttribute "simplification" ->
                Just . SimplificationAxiom' req lhs rhs sortVars
                    <$> withExcept DefinitionAttributeError (mkAttributes parsedAx)
        -- implies with equals but RHS not an and: malformed equation
        Syntax.KJImplies _ _req (Syntax.KJEquals _sort _ _lhs _rhs) ->
            throwE $ DefinitionAxiomError $ MalformedEquation parsedAx
        Syntax.KJExists{var, varSort, arg = Syntax.KJEquals{first = aVar, second = Syntax.KJApp{}}}
            | hasAttribute "functional" || hasAttribute "total"
            , aVar == Syntax.KJEVar{name = var, sort = varSort} -> do
                do
                    -- TODO assert that symbol `name` is indeed a total function (or a constructor)
                    pure Nothing
        Syntax.KJImplies
            _
            Syntax.KJAnd{first = con1@Syntax.KJApp{}, second = con2@Syntax.KJApp{}}
            Syntax.KJApp{name}
                | hasAttribute "constructor"
                , con1.name == con2.name
                , con1.name == name ->
                    -- no confusion same constructor. Could assert `name` is a constructor
                    pure Nothing
        Syntax.KJNot _ (Syntax.KJAnd{first = con1@Syntax.KJApp{}, second = con2@Syntax.KJApp{}})
            | hasAttribute "constructor"
            , con1.name /= con2.name ->
                -- no confusion different constructors. Could check whether con*.name are constructors
                pure Nothing
        Syntax.KJOr{}
            | hasAttribute "constructor" ->
                -- no junk
                pure Nothing
        Syntax.KJEquals{}
            | hasAttribute "assoc" -> pure Nothing -- could check symbol axiom.first.name
            | hasAttribute "comm" -> pure Nothing -- could check symbol axiom.first.name
            | hasAttribute "idem" -> pure Nothing -- could check axiom.first.name
            | hasAttribute "unit" -> pure Nothing -- could check axiom.first.name and the unit symbol in axiom.first.args
            | hasAttribute "overload" -> pure Nothing
            | hasAttribute "simplification" -- special case of injection simplification
            , Syntax.KJApp{name = sym1} <- axiom.first
            , sym1 == Syntax.Id "inj"
            , Syntax.KJApp{name = sym2} <- axiom.second
            , sym2 == Syntax.Id "inj" ->
                pure Nothing
        Syntax.KJBottom{sort = Syntax.SortApp _ []}
            | hasAttribute "constructor" ->
                pure Nothing
        -- anything else:  error, as the list should be comprehensive
        _ -> throwE $ DefinitionAxiomError $ UnexpectedAxiom parsedAx
  where
    hasAttribute name = isJust $ lookup (Syntax.Id name) attributes

    isVar Syntax.KJEVar{} = True
    isVar _other = False

    -- deconstructs function argument predicates (\and-chain of \in ended by \top)
    extractBinders ::
        Syntax.KorePattern ->
        Except DefinitionError [(Syntax.Id, Syntax.Sort, Syntax.KorePattern)]
    extractBinders = \case
        Syntax.KJTop{} ->
            pure []
        Syntax.KJIn{first = Syntax.KJEVar{name, sort}, second = term} ->
            pure [(name, sort, term)]
        Syntax.KJAnd{first = Syntax.KJIn _ _ Syntax.KJEVar{name, sort} term, second = rest} ->
            ((name, sort, term) :) <$> extractBinders rest
        other -> throwE $ DefinitionAxiomError $ MalformedArgumentBinder parsedAx other

internaliseAxiom ::
    PartialDefinition ->
    ParsedAxiom ->
    Except DefinitionError (Maybe AxiomResult)
internaliseAxiom (Partial partialDefinition) parsedAxiom =
    classifyAxiom parsedAxiom >>= maybe (pure Nothing) processAxiom
  where
    extractExistentials = \case
        Syntax.KJExists{var, varSort, arg} -> do
            ((var, varSort) :)
                <$> extractExistentials arg
        other -> (other, [])

    processAxiom :: AxiomData -> Except DefinitionError (Maybe AxiomResult)
    processAxiom = \case
        SubsortAxiom' Syntax.SortApp{name = Syntax.Id sub} Syntax.SortApp{name = Syntax.Id super} -> do
            when (sub == super) $
                throwE $
                    DefinitionSortError $
                        GeneralError ("Bad subsort rule " <> sub <> " < " <> super)
            pure $ Just $ SubsortAxiom (textToBS sub, textToBS super)
        SubsortAxiom' Syntax.SortVar{name = Syntax.Id sub} _ ->
            throwE $
                DefinitionSortError $
                    GeneralError ("Sort variable " <> sub <> " in subsort axiom")
        SubsortAxiom' _ Syntax.SortVar{name = Syntax.Id super} ->
            throwE $
                DefinitionSortError $
                    GeneralError ("Sort variable " <> super <> " in subsort axiom")
        RewriteRuleAxiomNoAlias' lhs rhs' attribs ->
            let (rhs, existentials) = extractExistentials rhs'
             in Just . RewriteRuleAxiom
                    <$> internaliseRewriteRuleNoAlias
                        partialDefinition
                        existentials
                        lhs
                        rhs
                        attribs
        RewriteRuleAxiom' alias args rhs' attribs ->
            let (rhs, existentials) = extractExistentials rhs'
             in Just . RewriteRuleAxiom
                    <$> internaliseRewriteRule
                        partialDefinition
                        existentials
                        (textToBS alias)
                        args
                        rhs
                        attribs
        SimplificationAxiom' requires lhs rhs sortVars attribs ->
            Just
                <$> internaliseSimpleEquation
                    partialDefinition
                    requires
                    lhs
                    rhs
                    sortVars
                    attribs
        FunctionAxiom' requires args lhs rhs sortVars attribs ->
            Just
                <$> internaliseFunctionEquation
                    partialDefinition
                    requires
                    args
                    lhs
                    rhs
                    sortVars
                    attribs

orFailWith :: Maybe a -> e -> Except e a
mbX `orFailWith` err = maybe (throwE err) pure mbX

internaliseRewriteRuleNoAlias ::
    KoreDefinition ->
    [(Id, Sort)] ->
    Syntax.KorePattern ->
    Syntax.KorePattern ->
    AxiomAttributes ->
    Except DefinitionError (RewriteRule k)
internaliseRewriteRuleNoAlias partialDefinition exs left right axAttributes = do
    let ref = sourceRef axAttributes
    -- prefix all variables in lhs and rhs with "Rule#" to avoid
    -- name clashes with patterns from the user
    -- filter out literal `Top` constraints
    lhs <-
        fmap (removeTops . Util.modifyVariables (Util.modifyVarName ("Rule#" <>))) $
            withExcept (DefinitionPatternError ref) $
                internalisePattern True Nothing partialDefinition left
    existentials' <- fmap Set.fromList $ withExcept (DefinitionPatternError ref) $ mapM mkVar exs
    let renameVariable v
            | v `Set.member` existentials' = Util.modifyVarName ("Ex#" <>) v
            | otherwise = Util.modifyVarName ("Rule#" <>) v
    rhs <-
        fmap (removeTops . Util.modifyVariables renameVariable) $
            withExcept (DefinitionPatternError ref) $
                internalisePattern True Nothing partialDefinition right
    let notPreservesDefinednessReasons =
            -- users can override the definedness computation by an explicit attribute
            if coerce axAttributes.preserving
                then []
                else
                    [ UndefinedSymbol s.name
                    | s <- Util.filterTermSymbols (not . Util.isDefinedSymbol) rhs.term
                    ]
        containsAcSymbols =
            Util.checkTermSymbols Util.checkSymbolIsAc lhs.term
        computedAttributes =
            ComputedAxiomAttributes{notPreservesDefinednessReasons, containsAcSymbols}
        existentials = Set.map (Util.modifyVarName ("Ex#" <>)) existentials'
    return
        RewriteRule
            { lhs = lhs.term
            , rhs = rhs.term
            , requires = lhs.constraints
            , ensures = rhs.constraints
            , attributes = axAttributes
            , computedAttributes
            , existentials
            }
  where
    mkVar (name, sort) = do
        variableSort <- lookupInternalSort Nothing partialDefinition.sorts right sort
        let variableName = textToBS name.getId
        pure $ Variable{variableSort, variableName}

internaliseRewriteRule ::
    KoreDefinition ->
    [(Id, Sort)] ->
    AliasName ->
    [Syntax.KorePattern] ->
    Syntax.KorePattern ->
    AxiomAttributes ->
    Except DefinitionError (RewriteRule k)
internaliseRewriteRule partialDefinition exs aliasName aliasArgs right axAttributes = do
    let ref = sourceRef axAttributes
    alias <-
        withExcept (DefinitionAliasError $ Text.decodeLatin1 aliasName) $
            Map.lookup aliasName partialDefinition.aliases
                `orFailWith` UnknownAlias aliasName
    args <-
        traverse
            ( withExcept (DefinitionPatternError ref)
                . internaliseTerm True Nothing partialDefinition
            )
            aliasArgs
    result <- expandAlias alias args

    -- prefix all variables in lhs and rhs with "Rule#" to avoid
    -- name clashes with patterns from the user
    -- filter out literal `Top` constraints
    lhs <-
        fmap (removeTops . Util.modifyVariables (Util.modifyVarName ("Rule#" <>))) $
            Util.retractPattern result
                `orFailWith` DefinitionTermOrPredicateError ref (PatternExpected result)
    existentials' <- fmap Set.fromList $ withExcept (DefinitionPatternError ref) $ mapM mkVar exs
    let renameVariable v
            | v `Set.member` existentials' = Util.modifyVarName ("Ex#" <>) v
            | otherwise = Util.modifyVarName ("Rule#" <>) v
    rhs <-
        fmap (removeTops . Util.modifyVariables renameVariable) $
            withExcept (DefinitionPatternError ref) $
                internalisePattern True Nothing partialDefinition right

    let notPreservesDefinednessReasons =
            -- users can override the definedness computation by an explicit attribute
            if coerce axAttributes.preserving
                then []
                else
                    [ UndefinedSymbol s.name
                    | s <- Util.filterTermSymbols (not . Util.isDefinedSymbol) rhs.term
                    ]
        containsAcSymbols =
            Util.checkTermSymbols Util.checkSymbolIsAc lhs.term
        computedAttributes =
            ComputedAxiomAttributes{notPreservesDefinednessReasons, containsAcSymbols}
        existentials = Set.map (Util.modifyVarName ("Ex#" <>)) existentials'
        attributes =
            axAttributes{concreteness = Util.modifyVarNameConcreteness ("Rule#" <>) axAttributes.concreteness}
    return
        RewriteRule
            { lhs = lhs.term
            , rhs = rhs.term
            , requires = lhs.constraints
            , ensures = rhs.constraints
            , attributes
            , computedAttributes
            , existentials
            }
  where
    mkVar (name, sort) = do
        variableSort <- lookupInternalSort Nothing partialDefinition.sorts right sort
        let variableName = textToBS name.getId
        pure $ Variable{variableSort, variableName}

expandAlias :: Alias -> [Def.Term] -> Except DefinitionError Def.TermOrPredicate
expandAlias alias currentArgs
    | length alias.args /= length currentArgs =
        throwE $
            DefinitionAliasError (Text.decodeLatin1 alias.name) $
                WrongAliasArgCount alias currentArgs
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

removeTops :: Def.Pattern -> Def.Pattern
removeTops p = p{Def.constraints = filter (/= Def.Top) p.constraints}

{- | Internalises simplification rules, for both term simplification
   (represented as a 'RewriteRule') and predicate simplification
   (represented as a 'PredicateEquation').

   Term simplifications may introduce undefined terms, or remove them
   erroneously, so the 'preservesDefinedness' check refers to both the
   LHS and the RHS term.
   Predicates have no problem with definedness, as a rule with a
   \bottom predicate will simply never apply
-}
internaliseSimpleEquation ::
    KoreDefinition -> -- context
    Syntax.KorePattern -> -- requires
    Syntax.KorePattern -> -- LHS
    Syntax.KorePattern -> -- And(RHS, ensures)
    [Syntax.Id] -> -- sort variables
    AxiomAttributes ->
    Except DefinitionError AxiomResult
internaliseSimpleEquation partialDef precond left right sortVars attrs
    | coerce attrs.simplification = do
        lhsIsTerm <- withExcept (DefinitionPatternError (sourceRef attrs)) $ isTermM left
        if lhsIsTerm
            then do
                lhs <- internalisePattern' $ Syntax.KJAnd left.sort left precond
                rhs <- internalisePattern' right
                let
                    -- checking the lhs term, too, as a safe approximation
                    -- (rhs may _introduce_ undefined, lhs may _hide_ it)
                    undefinedSymbols =
                        nub . concatMap (Util.filterTermSymbols (not . Util.isDefinedSymbol)) $
                            [lhs.term, rhs.term]
                    computedAttributes =
                        ComputedAxiomAttributes
                            { containsAcSymbols =
                                any (Util.checkTermSymbols Util.checkSymbolIsAc) [lhs.term, rhs.term]
                            , notPreservesDefinednessReasons =
                                if coerce attrs.preserving
                                    then []
                                    else map (UndefinedSymbol . (.name)) undefinedSymbols
                            }
                    attributes = attrs{concreteness = Util.modifyVarNameConcreteness ("Eq#" <>) attrs.concreteness}
                pure $
                    SimplificationAxiom
                        RewriteRule
                            { lhs = lhs.term
                            , rhs = rhs.term
                            , requires = lhs.constraints
                            , ensures = rhs.constraints
                            , attributes
                            , computedAttributes
                            , existentials = Set.empty
                            }
            else do
                target <- internalisePredicate' left
                conditions <- mapM internalisePredicate' $ explodeAnd precond
                rhs <- mapM internalisePredicate' $ explodeAnd right
                -- undefined predicates will invalidate the rule, no flags required
                let computedAttributes = ComputedAxiomAttributes False []
                pure $
                    PredicateSimplificationAxiom
                        PredicateEquation
                            { target
                            , conditions
                            , rhs
                            , attributes = attrs
                            , computedAttributes
                            }
    | otherwise = error "internaliseSimpleEquation should only be called for simplifications"
  where
    internalisePattern' =
        withExcept (DefinitionPatternError (sourceRef attrs))
            . fmap (removeTops . Util.modifyVariables (Util.modifyVarName ("Eq#" <>)))
            . internalisePattern True (Just sortVars) partialDef
    internalisePredicate' =
        withExcept (DefinitionPatternError (sourceRef attrs))
            . internalisePredicate True (Just sortVars) partialDef

{- | Internalises a function rule from its components that were matched
  before.

   Argument patterns are inlined, but checked to ensure they are
   always defined (conservative: only allowing constructors and total
   functions).  However, since function rules are anyway not allowed
   to contain nested function calls, this check will only detect AC
   symbols.

   Any function rule that contains any AC symbols in arguments is
   marked as not preserving definedness. Processing should abort when
   such a rule could match.
-}
internaliseFunctionEquation ::
    KoreDefinition -> -- context
    Syntax.KorePattern -> -- requires
    [(Syntax.Id, Syntax.Sort, Syntax.KorePattern)] -> -- argument binders
    Syntax.KorePattern -> -- LHS
    Syntax.KorePattern -> -- And(RHS, ensures)
    [Syntax.Id] -> -- sort variables
    AxiomAttributes ->
    Except DefinitionError AxiomResult
internaliseFunctionEquation partialDef requires args leftTerm right sortVars attrs = do
    -- internalise the LHS (LHS term and requires)
    left <- -- expected to be a simple term, f(X_1, X_2,..)
        withExcept (DefinitionPatternError (sourceRef attrs)) $
            internalisePattern True (Just sortVars) partialDef $
                Syntax.KJAnd leftTerm.sort leftTerm requires
    -- extract argument binders from predicates and inline in to LHS term
    argPairs <- mapM internaliseArg args
    let lhs =
            removeTops . Util.modifyVariables (Util.modifyVarName ("Eq#" <>)) $
                left{Def.term = Util.substituteInTerm (Map.fromList argPairs) left.term}
    rhs <- internaliseSide right
    let argsUndefined =
            concatMap (Util.filterTermSymbols (not . Util.isDefinedSymbol) . snd) argPairs
        rhsUndefined =
            Util.filterTermSymbols (not . Util.isDefinedSymbol) rhs.term
        containsAcSymbols =
            any (Util.checkTermSymbols Util.checkSymbolIsAc . snd) argPairs
        computedAttributes =
            ComputedAxiomAttributes
                { notPreservesDefinednessReasons =
                    -- users can override the definedness computation by an explicit attribute
                    -- we also assume that rules for total functions always preserve definedness
                    if coerce attrs.preserving || functionSymbolIsTotal lhs.term
                        then []
                        else [UndefinedSymbol s.name | s <- nub (argsUndefined <> rhsUndefined)]
                , containsAcSymbols
                }
        attributes =
            attrs{concreteness = Util.modifyVarNameConcreteness ("Eq#" <>) attrs.concreteness}
    pure $
        FunctionAxiom
            RewriteRule
                { lhs = lhs.term
                , rhs = rhs.term
                , requires = lhs.constraints
                , ensures = rhs.constraints
                , attributes
                , computedAttributes
                , existentials = Set.empty
                }
  where
    functionSymbolIsTotal = \case
        Def.SymbolApplication symbol _ _ -> symbol.attributes.symbolType == TotalFunction
        _ -> False

    internaliseSide =
        withExcept (DefinitionPatternError (sourceRef attrs))
            . fmap (removeTops . Util.modifyVariables (Util.modifyVarName ("Eq#" <>)))
            . internalisePattern True (Just sortVars) partialDef

    internaliseTerm' =
        withExcept (DefinitionPatternError (sourceRef attrs))
            . internaliseTerm True (Just sortVars) partialDef

    internaliseArg ::
        (Syntax.Id, Syntax.Sort, Syntax.KorePattern) ->
        Except DefinitionError (Def.Variable, Def.Term)
    internaliseArg (Syntax.Id name, sort, term) = do
        variableSort <-
            withExcept DefinitionSortError $
                internaliseSort (Set.fromList $ map (.getId) sortVars) partialDef.sorts sort
        (Def.Variable{variableSort, variableName = textToBS name},) <$> internaliseTerm' term

addToTheoryWith ::
    HasField "attributes" axiom AxiomAttributes =>
    (axiom -> TermIndex) ->
    [axiom] ->
    Theory axiom ->
    Theory axiom
addToTheoryWith termIndex axioms theory =
    let newTheory =
            Map.map groupByPriority
                . groupByTermIndex termIndex
                $ axioms
     in Map.unionWith (Map.unionWith (<>)) theory newTheory

groupByTermIndex :: (axiom -> TermIndex) -> [axiom] -> Map TermIndex [axiom]
groupByTermIndex termIndex axioms =
    let withTermIndexes = do
            axiom <- axioms
            let index = termIndex axiom
            return (index, axiom)
     in Map.fromAscList . groupSort $ withTermIndexes

groupByPriority ::
    HasField "attributes" axiom AxiomAttributes =>
    [axiom] ->
    Map Priority [axiom]
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
    attributes <- withExcept DefinitionAttributeError $ mkAttributes parsedSymbol
    let name = textToBS parsedSymbol.name.getId
        internalSymbol = Def.Symbol{name, sortVars, resultSort, argSorts, attributes}
    pure (name, internalSymbol)
  where
    knownVars = Set.fromList sortVarsT
    sortVarsT = map (.getId) parsedSymbol.sortVars
    sortVars = map textToBS sortVarsT

    check :: Syntax.Sort -> Except DefinitionError Def.Sort
    check =
        mapExcept (first DefinitionSortError)
            . internaliseSort knownVars sorts

{- | Computes all-pairs reachability in a directed graph given as an
   adjacency list mapping. Using a naive algorithm because the subsort
   graph will usually be broad and flat rather than deep.
-}
transitiveClosure :: forall k. Ord k => Map k (Set.Set k) -> Map k (Set.Set k)
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
    | DefinitionAttributeError Text
    | DefinitionSortError SortError
    | DefinitionPatternError SourceRef PatternError
    | DefinitionAliasError Text AliasError
    | DefinitionAxiomError AxiomError
    | DefinitionTermOrPredicateError SourceRef TermOrPredicateError
    | AddModuleError Text
    | ElemSymbolMalformed Def.Symbol
    | ElemSymbolNotFound Def.SymbolName
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
        DefinitionAttributeError msg ->
            pretty $ "Attribute error: " <> msg
        DefinitionSortError sortErr ->
            pretty $ "Sort error: " <> renderSortError sortErr
        DefinitionPatternError ref patErr ->
            "Pattern error in " <> pretty ref <> ": " <> pretty (show patErr)
        -- TODO define a pretty instance?
        DefinitionAliasError name err ->
            pretty $ "Alias error in " <> Text.unpack name <> ": " <> show err
        DefinitionAxiomError err ->
            "Bad rewrite rule " <> pretty err
        DefinitionTermOrPredicateError ref (PatternExpected p) ->
            "Expected a pattern in " <> pretty ref <> " but found a predicate: " <> pretty (show p)
        AddModuleError msg ->
            pretty $ "Add-module error: " <> msg
        ElemSymbolMalformed sym ->
            pretty $ "Element{} symbol is malformed: " <> show sym
        ElemSymbolNotFound sym ->
            pretty $ "Expected an element{} symbol " <> show sym

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
        DefinitionPatternError ref patErr ->
            ("Pattern error at " <> render ref <> " in definition") `withContext` [toJSON patErr]
        DefinitionAxiomError (MalformedRewriteRule rule) ->
            "Malformed rewrite rule" `withContext` [toJSON rule]
        DefinitionAxiomError (MalformedEquation rule) ->
            "Malformed equation" `withContext` [toJSON rule]
        DefinitionAxiomError (UnexpectedAxiom rule) ->
            "Unknown kind of axiom" `withContext` [toJSON rule]
        other ->
            object ["error" .= render other, "context" .= Null]
      where
        withContext :: Text -> [Value] -> Value
        withContext errMsg context =
            object ["error" .= errMsg, "context" .= context]

        render :: Pretty a => a -> Text
        render = renderOneLineText . pretty

data AliasError
    = UnknownAlias AliasName
    | WrongAliasSortCount ParsedAlias
    | WrongAliasArgCount Alias [Def.Term]
    | InconsistentAliasPattern [PatternError]
    deriving stock (Eq, Show)

data AxiomError
    = MalformedRewriteRule ParsedAxiom
    | MalformedEquation ParsedAxiom
    | UnexpectedAxiom ParsedAxiom
    | MalformedArgumentBinder ParsedAxiom Syntax.KorePattern
    deriving stock (Eq, Show)

instance Pretty AxiomError where
    pretty = \case
        MalformedRewriteRule rule ->
            "Malformed rewrite rule at " <> location rule
        MalformedEquation rule ->
            "Malformed equation at " <> location rule
        UnexpectedAxiom rule ->
            "Unknown kind of axiom at " <> location rule
        MalformedArgumentBinder rule pat ->
            pretty ("Malformed argument binder " <> show pat)
                <> " in function equation at "
                <> location rule
      where
        location :: ParsedAxiom -> Doc a
        location rule =
            either (const "unknown location") pretty $
                runExcept (Attributes.readLocation rule.attributes)

newtype TermOrPredicateError
    = PatternExpected Def.TermOrPredicate
    deriving stock (Eq, Show)
