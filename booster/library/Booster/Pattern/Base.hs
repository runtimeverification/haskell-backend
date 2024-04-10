{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Base (
    -- export everything, modules above can re-export only type names
    module Booster.Pattern.Base,
) where

import Booster.Definition.Attributes.Base (
    KCollectionMetadata (..),
    KCollectionSymbolNames (..),
    KListDefinition (..),
    KMapDefinition (..),
    KSetDefinition,
    SymbolAttributes (..),
    SymbolType (..),
    pattern CanBeEvaluated,
    pattern IsAssoc,
    pattern IsNotAssoc,
    pattern IsNotIdem,
    pattern IsNotMacroOrAlias,
 )
import Booster.Prettyprinter qualified as KPretty

import Booster.Util (decodeLabel')
import Control.DeepSeq (NFData (..))
import Data.Bifunctor (second)
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Data (Data)
import Data.Functor.Foldable
import Data.Hashable (Hashable)
import Data.Hashable qualified as Hashable
import Data.List as List (foldl1', sort)
import Data.Set (Set, fromList, toList)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift (..))
import Prettyprinter (Pretty (..))
import Prettyprinter qualified as Pretty

type VarName = ByteString
type SymbolName = ByteString
type SortName = ByteString

{- | A term has a particular 'Sort', which is part of a definition.
  Sorts can be subsorts of others (not represented in the definition).
-}
data Sort
    = -- | sort constructor, potentially with arguments
      SortApp SortName [Sort]
    | -- | sort variable (symbolic)
      SortVar VarName
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

pattern SortBool, SortInt, SortK, SortKItem, SortBytes, SortSet, SortMap :: Sort
pattern SortBool = SortApp "SortBool" []
pattern SortInt = SortApp "SortInt" []
pattern SortK = SortApp "SortK" []
pattern SortKItem = SortApp "SortKItem" []
pattern SortSet = SortApp "SortSet" []
pattern SortMap = SortApp "SortMap" []
pattern SortBytes = SortApp "SortBytes" []

-- | A variable for symbolic execution or for terms in a rule.
data Variable = Variable
    { variableSort :: Sort
    , variableName :: VarName
    }
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

data Symbol = Symbol
    { name :: SymbolName
    , sortVars :: [VarName]
    , argSorts :: [Sort]
    , resultSort :: Sort
    , attributes :: SymbolAttributes
    }
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

{- | A term consists of an AST of constructors and function calls, as
   well as domain values (tokens and built-in types) and (element)
   variables.
   This is anything that can be part of a K configuration.

   This codebase deliberately does not include built-in types.
-}
data TermF t
    = AndTermF t t
    | SymbolApplicationF Symbol [Sort] [t]
    | DomainValueF Sort ByteString
    | VarF Variable
    | -- | injection node with source and target sort: "intermediate"
      -- sorts between source and target are shortened out.
      InjectionF Sort Sort t
    | KMapF KMapDefinition [(t, t)] (Maybe t)
    | -- | internal List
      KListF
        KListDefinition -- metadata
        [t] -- head elements
        (Maybe (t, [t])) -- optional (symbolic) middle and tail elements
    | -- | internal set
      KSetF
        KSetDefinition -- metadata, identical to KListDefinition
        [t] -- known elements (no duplicate check)
        (Maybe t) -- optional symbolic rest
    deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

{- | Term attributes are synthetic (bottom-up) attributes that cache
   information about a term to avoid unnecessary AST
   traversals. Attributes are computed when terms are constructed (see
   patterns below).
-}
data TermAttributes = TermAttributes
    { variables :: !(Set Variable)
    , isEvaluated :: !Bool
    -- ^ false for function calls, true for
    -- variables, recursive through AndTerm
    , hash :: !Int
    , isConstructorLike :: !Bool
    , canBeEvaluated :: !Bool
    -- ^ false for function calls, variables, and AndTerms
    }
    deriving stock (Eq, Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData, Hashable)

instance Lift (Set Variable) where
    lift s = let s' = toList s in [|fromList s'|]
    liftTyped s = let s' = toList s in [||fromList s'||]
instance Semigroup TermAttributes where
    a1 <> a2 =
        TermAttributes
            { variables = a1.variables <> a2.variables
            , isEvaluated = a1.isEvaluated && a2.isEvaluated
            , hash = 0
            , isConstructorLike = a1.isConstructorLike && a2.isConstructorLike
            , canBeEvaluated = a1.canBeEvaluated && a2.canBeEvaluated
            }

instance Monoid TermAttributes where
    mempty = TermAttributes Set.empty True 0 False True

-- | A term together with its attributes.
data Term = Term TermAttributes (TermF Term)
    deriving stock (Ord, Show, Generic, Data, Lift)
    deriving anyclass (NFData)

instance Eq Term where
    Term TermAttributes{hash = hash1} t1f == Term TermAttributes{hash = hash2} t2f =
        hash1 == hash2 && t1f == t2f -- compare directly to cater for collisions

instance Hashable Term where
    hash (Term TermAttributes{hash} _) = hash

type instance Base Term = TermF

instance Recursive Term where
    project (Term _ t) = t

getAttributes :: Term -> TermAttributes
getAttributes (Term a _) = a

unitSymbol, concatSymbol :: KCollectionMetadata -> Symbol
unitSymbol def =
    Symbol
        { name = symbolNames.unitSymbolName
        , sortVars = []
        , argSorts = []
        , resultSort = SortApp collectionSort []
        , attributes =
            SymbolAttributes
                { symbolType = TotalFunction
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , collectionMetadata = Just def
                , smt = Nothing
                }
        }
  where
    (symbolNames, collectionSort) =
        case def of
            KMapMeta mapDef -> (mapDef.symbolNames, mapDef.mapSortName)
            KListMeta listDef -> (listDef.symbolNames, listDef.listSortName)
            KSetMeta setDef -> (setDef.symbolNames, setDef.listSortName)
concatSymbol def =
    Symbol
        { name = symbolNames.concatSymbolName
        , sortVars = []
        , argSorts = [SortApp collectionSort [], SortApp collectionSort []]
        , resultSort = SortApp collectionSort []
        , attributes =
            SymbolAttributes
                { symbolType
                , isIdem = IsNotIdem
                , isAssoc = IsAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , collectionMetadata = Just def
                , smt = Nothing
                }
        }
  where
    (symbolNames, collectionSort, symbolType) =
        case def of
            KMapMeta mapDef -> (mapDef.symbolNames, mapDef.mapSortName, PartialFunction)
            KListMeta listDef -> (listDef.symbolNames, listDef.listSortName, TotalFunction)
            KSetMeta listDef -> (listDef.symbolNames, listDef.listSortName, PartialFunction)

kmapElementSymbol :: KMapDefinition -> Symbol
kmapElementSymbol def =
    Symbol
        { name = def.symbolNames.elementSymbolName
        , sortVars = []
        , argSorts = [SortApp def.keySortName [], SortApp def.elementSortName []]
        , resultSort = SortApp def.mapSortName []
        , attributes =
            SymbolAttributes
                { symbolType = TotalFunction
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , collectionMetadata = Just $ KMapMeta def
                , smt = Nothing
                }
        }

klistElementSymbol :: KListDefinition -> Symbol
klistElementSymbol def =
    Symbol
        { name = def.symbolNames.elementSymbolName
        , sortVars = []
        , argSorts = [SortApp def.elementSortName []]
        , resultSort = SortApp def.listSortName []
        , attributes =
            SymbolAttributes
                { symbolType = TotalFunction
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , collectionMetadata = Just $ KListMeta def
                , smt = Nothing
                }
        }

-- this function is marked unsafe because we won't get the same thing if we externalise and then internalise again.
-- this is because of the pattern synonym smart constructor for SymbolApplication, which checks if the current symbol is a KMap symbol
-- in which case it forces us back into a KMap. in order to not loop forever, we forget the kmap-ness in the function below
externaliseKmapUnsafe :: KMapDefinition -> [(Term, Term)] -> Maybe Term -> Term
externaliseKmapUnsafe def keyVals rest =
    case (keyVals, rest) of
        ([], Nothing) -> unit
        ([], Just r) -> r
        ((cK, cV) : cs, Nothing) ->
            foldr
                (\(k, v) r -> (k |-> v) `con` r)
                (cK |-> cV)
                cs
        (_, Just s) ->
            foldr
                (\(k, v) r -> (k |-> v) `con` r)
                s
                keyVals
  where
    unit = SymbolApplication (stripCollectionMetadata $ unitSymbol $ KMapMeta def) [] []
    k |-> v = SymbolApplication (stripCollectionMetadata $ kmapElementSymbol def) [] [k, v]
    a `con` b = SymbolApplication (stripCollectionMetadata $ concatSymbol $ KMapMeta def) [] [a, b]
{-# INLINE externaliseKmapUnsafe #-}

stripCollectionMetadata :: Symbol -> Symbol
stripCollectionMetadata s@Symbol{attributes = attrs} =
    s{attributes = attrs{collectionMetadata = Nothing}}

internaliseKmap :: KMapDefinition -> Term -> ([(Term, Term)], Maybe Term)
internaliseKmap def@KMapDefinition{symbolNames = names} = \case
    SymbolApplication s _ []
        | s.name == names.unitSymbolName -> ([], Nothing)
    SymbolApplication s _ [k, v]
        | s.name == names.elementSymbolName -> ([(k, v)], Nothing)
    SymbolApplication s _ [l, r]
        | s.name == names.concatSymbolName -> combine (internaliseKmap def l) (internaliseKmap def r)
    KMap def' keyVals rest
        | def == def' -> (keyVals, rest)
    other -> ([], Just other) -- do we want to recurse into this term in case there are some maps under e.g. function symbol??
  where
    concatSym = concatSymbol (KMapMeta def)
    combine (conc1, sym1) (conc2, sym2) =
        ( conc1 ++ conc2
        , case (sym1, sym2) of
            (Nothing, b) -> b
            (a, Nothing) -> a
            (Just a@(Term aAttribs _), Just b@(Term bAttribs _)) ->
                -- directly construct the internal term with functor to avoid a loop
                let attribs =
                        (aAttribs <> bAttribs)
                            { isEvaluated = False
                            , hash =
                                Hashable.hash
                                    ( "SymbolApplication" :: ByteString
                                    , concatSym
                                    , map hash [aAttribs, bAttribs]
                                    )
                            , isConstructorLike = False
                            }
                 in Just $ Term attribs $ SymbolApplicationF concatSym [] [a, b]
        )

{- | try to represent a list-returning symbol application as an
  internal list with head, optional middle and optional tail (empty
  list otherwise).

  In case of a concatenation, we might not succeed in representing the
  result as the internal list type, and will construct the result
  using list concatenation instead.
-}
internaliseKList :: KListDefinition -> Term -> Term
internaliseKList def = \case
    SymbolApplication s _ []
        | s.name == def.symbolNames.unitSymbolName -> KList def [] Nothing
    SymbolApplication s _ [x]
        | s.name == def.symbolNames.elementSymbolName -> KList def [x] Nothing
    SymbolApplication concatSym _ [x, y]
        | concatSym.name == def.symbolNames.concatSymbolName ->
            case (internaliseKList def x, internaliseKList def y) of
                -- try to combine cases that can be represented as `heads mid tails`
                (KList def1 hds1 rst1, KList def2 hds2 rst2)
                    | def1 /= def2 -> inconsistent def1 def2
                    | def /= def1 -> inconsistent def def1
                    | Nothing <- rst1
                    , Nothing <- rst2 ->
                        KList def1 (hds1 <> hds2) Nothing
                    | Nothing <- rst1 ->
                        KList def1 (hds1 <> hds2) rst2
                    | Nothing <- rst2 ->
                        KList def1 hds1 $ fmap (second (<> hds2)) rst1
                -- otherwise neither mid1 nor mid2 are trivial, we
                -- reconstruct concat expression.
                (a@KList{}, b@KList{}) ->
                    let attribs = concatAttribs (getAttributes a) (getAttributes b)
                     in Term attribs $ SymbolApplicationF concatSym [] [a, b]
                -- One of the terms is a fully concrete KList and
                -- the other is something else: combine to a KList
                (KList def1 heads Nothing, nonKList)
                    | def /= def1 -> inconsistent def def1
                    | otherwise ->
                        KList def heads (Just (nonKList, []))
                (nonKList, KList def1 tails Nothing)
                    | def /= def1 -> inconsistent def def1
                    | otherwise ->
                        KList def [] (Just (nonKList, tails))
                -- two non-KList terms, keep the concat expression
                (a@(Term aAttribs _), b@(Term bAttribs _)) ->
                    let attribs = concatAttribs aAttribs bAttribs
                     in Term attribs $ SymbolApplicationF concatSym [] [a, b]
      where
        inconsistent d1 d2 = error $ "Inconsistent list definitions " <> show (d1, d2)
        concatAttribs :: TermAttributes -> TermAttributes -> TermAttributes
        concatAttribs aAttribs bAttribs =
            (aAttribs <> bAttribs)
                { isEvaluated = False
                , hash =
                    Hashable.hash
                        ( "SymbolApplication" :: ByteString
                        , concatSym
                        , map hash [aAttribs, bAttribs]
                        )
                , isConstructorLike = False
                }
    other -> other

{- | reconstructs a list-constructing symbol application nest from an
   internal list representation.

   This is not a precise inverse of the above internalisation because
   the list concatenation becomes right-biased as much as possible.

   Assumes that mid is a list type but not KList (ensured by internalisation).
-}
externaliseKList :: KListDefinition -> [Term] -> Maybe (Term, [Term]) -> Term
externaliseKList def heads optRest
    | Nothing <- optRest =
        concatList $ map singleton heads
    | Just (mid, tails) <- optRest =
        concatList $ map singleton heads <> (mid : map singleton tails)
  where
    elemSym = stripCollectionMetadata $ klistElementSymbol def
    emptyList = SymbolApplication (stripCollectionMetadata $ unitSymbol $ KListMeta def) [] []
    concatSym = stripCollectionMetadata $ concatSymbol $ KListMeta def

    singleton :: Term -> Term
    singleton = SymbolApplication elemSym [] . (: [])

    -- concatenate ListItem terms or lists (right-biased)
    concatList [] = emptyList
    concatList xs =
        foldr1 (\a b -> SymbolApplication concatSym [] [a, b]) xs

internaliseKSet :: KSetDefinition -> Term -> Term
internaliseKSet def = \case
    SymbolApplication s _ []
        | s.name == def.symbolNames.unitSymbolName -> KSet def [] Nothing
    SymbolApplication s _ [x]
        | s.name == def.symbolNames.elementSymbolName -> KSet def [x] Nothing
    SymbolApplication concatSym _ [x, y]
        | concatSym.name == def.symbolNames.concatSymbolName ->
            case (internaliseKSet def x, internaliseKSet def y) of
                (KSet def1 elems1 rest1, KSet def2 elems2 rest2)
                    | def1 /= def2 ->
                        error $ "Inconsistent set definition " <> show (def1, def2)
                    | def1 /= def ->
                        error $ "Inconsistent set definition " <> show (def1, def)
                    | Nothing <- rest1 ->
                        KSet def (List.sort $ elems1 <> elems2) rest2
                    | Nothing <- rest2 ->
                        KSet def (List.sort $ elems1 <> elems2) rest1
                    | Just r1 <- rest1
                    , Just r2 <- rest2 ->
                        KSet
                            def
                            (List.sort $ elems1 <> elems2)
                            (Just $ SymbolApplication concatSym [] [r1, r2])
                (KSet def1 elems1 rest1, other2)
                    | def1 /= def -> error $ "Inconsistent set definition " <> show (def1, def)
                    | Nothing <- rest1 ->
                        KSet def elems1 (Just other2)
                    | Just r1 <- rest1 ->
                        KSet def elems1 (Just $ SymbolApplication concatSym [] [r1, other2])
                (other1, KSet def2 elems2 rest2)
                    | def2 /= def -> error $ "Inconsistent set definition " <> show (def2, def)
                    | Nothing <- rest2 ->
                        KSet def elems2 (Just other1)
                    | Just r2 <- rest2 ->
                        KSet def elems2 (Just $ SymbolApplication concatSym [] [other1, r2])
                (other1, other2) ->
                    SymbolApplication (stripCollectionMetadata concatSym) [] [other1, other2]
    other -> other

externaliseKSet :: KSetDefinition -> [Term] -> Maybe Term -> Term
externaliseKSet def elements optRest
    | Nothing <- optRest =
        concatSet $ map singleton elements
    | Just rest <- optRest =
        concatSet $ map singleton elements <> [rest]
  where
    elemSym = stripCollectionMetadata $ klistElementSymbol def
    concatSym = stripCollectionMetadata $ concatSymbol $ KSetMeta def

    emptySet = SymbolApplication (stripCollectionMetadata $ unitSymbol $ KSetMeta def) [] []

    singleton x = SymbolApplication elemSym [] [x]

    concatSet [] = emptySet
    concatSet xs =
        foldr1 (\a b -> SymbolApplication concatSym [] [a, b]) xs

instance Corecursive Term where
    embed (AndTermF t1 t2) = AndTerm t1 t2
    embed (SymbolApplicationF s ss ts) = SymbolApplication s ss ts
    embed (DomainValueF s t) = DomainValue s t
    embed (VarF v) = Var v
    embed (InjectionF source target t) = Injection source target t
    embed (KMapF def conc sym) = KMap def conc sym
    embed (KListF def heads rest) = KList def heads rest
    embed (KSetF def heads rest) = KSet def heads rest

-- smart term constructors, as bidirectional patterns
pattern AndTerm :: Term -> Term -> Term
pattern AndTerm t1 t2 <- Term _ (AndTermF t1 t2)
    where
        AndTerm t1@(Term a1 _) t2@(Term a2 _) =
            Term
                (a1 <> a2)
                    { hash = Hashable.hash ("AndTerm" :: ByteString, hash a1, hash a2)
                    , isConstructorLike = False
                    -- irrelevant, since anyway we never allow
                    -- AndTerm as a replacement in a match
                    }
                $ AndTermF t1 t2

pattern SymbolApplication :: Symbol -> [Sort] -> [Term] -> Term
pattern SymbolApplication sym sorts args <- Term _ (SymbolApplicationF sym sorts args)
    where
        SymbolApplication sym sorts args
            | sym == injectionSymbol
            , [source, target] <- sorts
            , [arg] <- args =
                Injection source target arg
            | Just (KMapMeta def) <- sym.attributes.collectionMetadata =
                let result =
                        internaliseKmap def $ Term mempty $ SymbolApplicationF sym sorts args
                 in case result of
                        ([], Just rest) -> rest -- eliminate useless nesting
                        (keyVals, rest) -> KMap def keyVals rest
            | Just (KListMeta def) <- sym.attributes.collectionMetadata =
                internaliseKList def $ Term mempty $ SymbolApplicationF sym sorts args
            | Just (KSetMeta def) <- sym.attributes.collectionMetadata =
                internaliseKSet def $ Term mempty $ SymbolApplicationF sym sorts args
            | otherwise =
                let argAttributes
                        | null args = mempty
                        -- avoid using default isConstructorLike = False
                        -- if there are arg.s
                        | otherwise = foldl1' (<>) $ map getAttributes args
                    symIsConstructor =
                        sym.attributes.symbolType `elem` [Constructor, SortInjection]
                 in Term
                        argAttributes
                            { isEvaluated =
                                -- Constructors and injections are
                                -- evaluated if their arguments are.
                                -- Function calls are not evaluated.
                                symIsConstructor && argAttributes.isEvaluated
                            , hash =
                                Hashable.hash ("SymbolApplication" :: ByteString, sym, sorts, map (hash . getAttributes) args)
                            , isConstructorLike =
                                symIsConstructor && argAttributes.isConstructorLike
                            , canBeEvaluated =
                                CanBeEvaluated == sym.attributes.hasEvaluators && argAttributes.canBeEvaluated
                            }
                        (SymbolApplicationF sym sorts args)

pattern DomainValue :: Sort -> ByteString -> Term
pattern DomainValue s value <- Term _ (DomainValueF s value)
    where
        DomainValue s value =
            Term
                mempty
                    { hash = Hashable.hash ("DomainValue" :: ByteString, s, value)
                    , isConstructorLike = True
                    }
                $ DomainValueF s value

pattern Var :: Variable -> Term
pattern Var v <- Term _ (VarF v)
    where
        Var v =
            Term
                mempty
                    { variables = Set.singleton v
                    , hash = Hashable.hash ("Var" :: ByteString, v)
                    }
                $ VarF v

pattern Injection :: Sort -> Sort -> Term -> Term
pattern Injection source target t <- Term _ (InjectionF source target t)
    where
        Injection source target t =
            case t of
                Injection source' target' sub'
                    | source == target' ->
                        Injection source' target sub'
                    | otherwise ->
                        error $ "Unexpected sort injection:" <> show t -- ???
                _other ->
                    let argAttribs = getAttributes t
                        attribs =
                            argAttribs
                                { hash = Hashable.hash ("Injection" :: ByteString, source, target, hash argAttribs)
                                }
                     in Term attribs $ InjectionF source target t

pattern KMap :: KMapDefinition -> [(Term, Term)] -> Maybe Term -> Term
pattern KMap def keyVals rest <- Term _ (KMapF def keyVals rest)
    where
        KMap def keyVals rest =
            let argAttributes =
                    case (keyVals, rest) of
                        ([], Nothing) -> mempty
                        ([], Just s) -> getAttributes s
                        (_ : _, Nothing) -> foldl1' (<>) $ concatMap (\(k, v) -> [getAttributes k, getAttributes v]) keyVals
                        (_ : _, Just r) -> foldr (<>) (getAttributes r) $ concatMap (\(k, v) -> [getAttributes k, getAttributes v]) keyVals
                (keyVals', rest') = case rest of
                    Just (KMap def' kvs r) | def' == def -> (kvs, r)
                    r -> ([], r)
             in Term
                    argAttributes
                        { isEvaluated =
                            -- Constructors and injections are evaluated if their arguments are.
                            -- Function calls are not evaluated.
                            argAttributes.isEvaluated
                        , hash =
                            Hashable.hash
                                ( "KMap" :: ByteString
                                , def
                                , map (\(k, v) -> (hash $ getAttributes k, hash $ getAttributes v)) keyVals
                                , hash . getAttributes <$> rest
                                )
                        , isConstructorLike =
                            argAttributes.isConstructorLike
                        , canBeEvaluated =
                            argAttributes.canBeEvaluated
                        }
                    $ KMapF def (Set.toList $ Set.fromList $ keyVals ++ keyVals') rest'

pattern KList :: KListDefinition -> [Term] -> Maybe (Term, [Term]) -> Term
pattern KList def heads rest <- Term _ (KListF def heads rest)
    where
        KList def heads rest =
            let argAttributes =
                    case (heads, rest) of
                        ([], Nothing) ->
                            mempty
                        (nonEmpty, Nothing) ->
                            foldl1' (<>) $ map getAttributes nonEmpty
                        (_, Just (m, tails)) ->
                            foldr ((<>) . getAttributes) (getAttributes m) $ heads <> tails
                (newHeads, newRest) = case rest of
                    Just (KList def' heads' rest', tails)
                        | def' /= def ->
                            error $ "Inconsistent list definition" <> show (def, def')
                        | otherwise ->
                            maybe
                                (heads <> heads' <> tails, Nothing)
                                (\(m, ts) -> (heads <> heads', Just (m, ts <> tails)))
                                rest'
                    other -> (heads, other)
             in Term
                    argAttributes
                        { hash =
                            Hashable.hash
                                ( "KList" :: ByteString
                                , def
                                , map (hash . getAttributes) heads
                                , fmap (hash . getAttributes . fst) rest
                                , fmap (map (hash . getAttributes) . snd) rest
                                )
                        }
                    $ KListF def newHeads newRest

pattern KSet :: KSetDefinition -> [Term] -> Maybe Term -> Term
pattern KSet def elements rest <- Term _ (KSetF def elements rest)
    where
        KSet def elements rest =
            let argAttributes
                    | Nothing <- rest
                    , null elements =
                        mempty
                    | Nothing <- rest =
                        foldl1' (<>) $ map getAttributes elements
                    | Just r <- rest =
                        foldr ((<>) . getAttributes) (getAttributes r) elements
                (newElements, newRest) = case rest of
                    Just (KSet def' elements' rest')
                        | def /= def' ->
                            error $ "Inconsistent set definition " <> show (def, def')
                        | otherwise ->
                            (Set.toList . Set.fromList $ elements <> elements', rest')
                    other -> (elements, other)
             in Term
                    argAttributes
                        { hash =
                            Hashable.hash
                                ( "KSet" :: ByteString
                                , def
                                , map (hash . getAttributes) elements
                                , fmap (hash . getAttributes) rest
                                )
                        }
                    $ KSetF def newElements newRest
{-# COMPLETE AndTerm, SymbolApplication, DomainValue, Var, Injection, KMap, KList, KSet #-}

-- hard-wired injection symbol
injectionSymbol :: Symbol
injectionSymbol =
    Symbol
        { name = "inj"
        , sortVars = ["From", "To"]
        , argSorts = [SortVar "From"]
        , resultSort = SortVar "To"
        , attributes =
            SymbolAttributes
                { symbolType = SortInjection
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , collectionMetadata = Nothing
                , smt = Nothing
                }
        }

-- convenience patterns
pattern DV :: Sort -> Symbol
pattern DV sort <- Symbol "\\dv" _ _ sort _

pattern DotDotDot :: Term
pattern DotDotDot = DomainValue (SortApp "internalDummySort" []) "..."

{- | A predicate describes constraints on terms. It will always evaluate
   to 'TrueBool' or 'FalseBool'. Notice that 'Predicate's don't have a sort.
-}
newtype Predicate = Predicate Term
    deriving stock (Eq, Ord, Show, Generic, Data)
    deriving anyclass (NFData)

newtype Ceil = Ceil Term
    deriving stock (Eq, Ord, Show, Generic, Data)
    deriving anyclass (NFData)

-- kseq{}(inj{<sort>, SortKItem{}}(<a>),dotk{}()
pattern KSeq :: Sort -> Term -> Term
pattern KSeq sort a =
    SymbolApplication
        ( Symbol
                "kseq"
                []
                [SortKItem, SortK]
                SortK
                (SymbolAttributes Constructor IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing Nothing)
            )
        []
        [ Injection sort SortKItem a
            , SymbolApplication
                ( Symbol
                        "dotk"
                        []
                        []
                        SortK
                        (SymbolAttributes Constructor IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing Nothing)
                    )
                []
                []
            ]

--------------------

-- | A term (configuration) constrained by a number of predicates.
data Pattern = Pattern
    { term :: Term
    , constraints :: !(Set Predicate)
    , ceilConditions :: ![Ceil]
    }
    deriving stock (Eq, Ord, Show, Generic, Data)
    deriving anyclass (NFData)

pattern Pattern_ :: Term -> Pattern
pattern Pattern_ t <- Pattern t _ _
    where
        Pattern_ t = Pattern t mempty mempty

-- used for printing the string as it appears (with codepoints)
prettyBS :: ByteString -> Pretty.Doc a
prettyBS = Pretty.pretty . Text.decodeUtf8

instance Pretty Term where
    pretty = \case
        AndTerm t1 t2 ->
            pretty t1 <> "/\\" <> pretty t2
        SymbolApplication symbol _sortParams args ->
            pretty (Text.replace "Lbl" "" $ Text.decodeUtf8 $ decodeLabel' symbol.name)
                <> KPretty.argumentsP args
        DotDotDot -> "..."
        DomainValue _sort bs -> pretty . show . Text.decodeLatin1 . shortenBS $ bs
        Var var -> pretty var
        Injection _source _target t' -> pretty t'
        KMap _attrs keyVals rest ->
            Pretty.braces . Pretty.hsep . Pretty.punctuate Pretty.comma $
                [pretty k <> "->" <> pretty v | (k, v) <- keyVals]
                    ++ maybe [] ((: []) . pretty) rest
        KList _meta heads (Just (mid, tails)) ->
            Pretty.hsep $
                Pretty.punctuate
                    " +"
                    [renderList heads, pretty mid, renderList tails]
        KList _meta [] Nothing ->
            "[]"
        KList _meta heads Nothing ->
            renderList heads
        KSet _meta [] Nothing -> "{}"
        KSet _meta [] (Just rest) -> pretty rest
        KSet _meta es rest ->
            (Pretty.braces . Pretty.hsep . Pretty.punctuate Pretty.comma $ map pretty es)
                Pretty.<+> maybe mempty ((" ++ " <>) . pretty) rest
      where
        renderList l
            | null l = mempty
            | otherwise =
                Pretty.brackets . Pretty.hsep . Pretty.punctuate Pretty.comma $
                    map pretty l

        -- shorten domain value ByteString to a readable length
        shortenBS dv =
            let cutoff = 16
             in if BS.length dv < cutoff then dv else BS.take cutoff dv <> "...truncated"

instance Pretty Sort where
    pretty (SortApp name params) =
        prettyBS name <> KPretty.parametersP params
    pretty (SortVar name) =
        prettyBS name

instance Pretty Variable where
    pretty var =
        prettyBS (decodeLabel' var.variableName)
            <> Pretty.colon
            <> pretty var.variableSort

instance Pretty Predicate where
    pretty (Predicate t) = pretty t

instance Pretty Ceil where
    pretty (Ceil t) =
        "\\ceil"
            <> KPretty.noParameters
            <> KPretty.argumentsP [t]

instance Pretty Pattern where
    pretty patt =
        Pretty.vsep $
            [ "Term:"
            , Pretty.indent 4 $ pretty patt.term
            , "Conditions:"
            ]
                <> fmap (Pretty.indent 4 . pretty) (Set.toList patt.constraints)
                <> fmap (Pretty.indent 4 . pretty) patt.ceilConditions
