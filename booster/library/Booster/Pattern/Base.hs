{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Base (
    -- export everything, modules above can re-export only type names
    module Booster.Pattern.Base,
) where

import Booster.Definition.Attributes.Base (
    KMapAttributes (..),
    KMapDefinition (..),
    SymbolAttributes (..),
    SymbolType (..),
    pattern IsAssoc,
    pattern IsNotAssoc,
    pattern IsNotIdem,
    pattern IsNotMacroOrAlias,
 )
import Booster.Prettyprinter qualified as KPretty
import Control.DeepSeq (NFData (..))
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Either (fromRight)
import Data.Functor.Foldable
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Hashable (Hashable)
import Data.Hashable qualified as Hashable
import Data.List (foldl1')
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
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
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

pattern SortBool :: Sort
pattern SortBool = SortApp "SortBool" []

-- | A variable for symbolic execution or for terms in a rule.
data Variable = Variable
    { variableSort :: Sort
    , variableName :: VarName
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

data Symbol = Symbol
    { name :: SymbolName
    , sortVars :: [VarName]
    , argSorts :: [Sort]
    , resultSort :: Sort
    , attributes :: SymbolAttributes
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

{- | A term consists of an AST of constructors and function calls, as
   well as domain values (tokens and built-in types) and (element)
   variables.
   This is anything that can be part of a K configuration.

   Deliberately kept simple in this codebase (leaving out built-in
   types and containers).
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
    deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
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
    -- ^ false for function calls, variables, and AndTerms
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

instance Semigroup TermAttributes where
    a1 <> a2 =
        TermAttributes
            { variables = a1.variables <> a2.variables
            , isEvaluated = a1.isEvaluated && a2.isEvaluated
            , hash = 0
            , isConstructorLike = a1.isConstructorLike && a2.isConstructorLike
            }

instance Monoid TermAttributes where
    mempty = TermAttributes Set.empty True 0 False

-- | A term together with its attributes.
data Term = Term TermAttributes (TermF Term)
    deriving stock (Ord, Show, Generic)
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

kmapUnitSymbol, kmapConcatSymbol, kmapElementSymbol :: KMapDefinition -> Symbol
kmapUnitSymbol def =
    Symbol
        { name = def.symbolNames.unitSymbolName
        , sortVars = []
        , argSorts = []
        , resultSort = SortApp def.mapSortName []
        , attributes =
            SymbolAttributes
                { symbolType = TotalFunction
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , isKMapSymbol = Just def
                }
        }
kmapConcatSymbol def =
    Symbol
        { name = def.symbolNames.concatSymbolName
        , sortVars = []
        , argSorts = [SortApp def.mapSortName [], SortApp def.mapSortName []]
        , resultSort = SortApp def.mapSortName []
        , attributes =
            SymbolAttributes
                { symbolType = PartialFunction
                , isIdem = IsNotIdem
                , isAssoc = IsAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , isKMapSymbol = Just def
                }
        }
kmapElementSymbol def =
    Symbol
        { name = def.symbolNames.elementSymbolName
        , sortVars = []
        , argSorts = [SortApp def.keySortName [], SortApp def.elementSortName []]
        , resultSort = SortApp def.mapSortName []
        , attributes =
            SymbolAttributes
                { symbolType = PartialFunction
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , isKMapSymbol = Just def
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
    stripIsKmap :: Symbol -> Symbol
    stripIsKmap s@Symbol{attributes = attrs} = s{attributes = attrs{isKMapSymbol = Nothing}}

    unit = SymbolApplication (stripIsKmap $ kmapUnitSymbol def) [] []
    k |-> v = SymbolApplication (stripIsKmap $ kmapElementSymbol def) [] [k, v]
    a `con` b = SymbolApplication (stripIsKmap $ kmapConcatSymbol def) [] [a, b]
{-# INLINE externaliseKmapUnsafe #-}

internaliseKmap :: KMapDefinition -> Term -> ([(Term, Term)], Maybe Term)
internaliseKmap def@KMapDefinition{symbolNames = KMapAttributes{elementSymbolName, concatSymbolName, unitSymbolName}} = \case
    SymbolApplication s _ []
        | s.name == unitSymbolName -> ([], Nothing)
    SymbolApplication s _ [k, v]
        | s.name == elementSymbolName -> ([(k, v)], Nothing)
    SymbolApplication s _ [l, r]
        | s.name == concatSymbolName -> combine (internaliseKmap def l) (internaliseKmap def r)
    KMap def' keyVals rest
        | def == def' -> (keyVals, rest)
    other -> ([], Just other) -- do we want to recurse into this term in case there are some maps under e.g. function symbol??
  where
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
                                    , kmapConcatSymbol def
                                    , map hash [aAttribs, bAttribs]
                                    )
                            , isConstructorLike = False
                            }
                 in Just $ Term attribs $ SymbolApplicationF (kmapConcatSymbol def) [] [a, b]
        )

instance Corecursive Term where
    embed (AndTermF t1 t2) = AndTerm t1 t2
    embed (SymbolApplicationF s ss ts) = SymbolApplication s ss ts
    embed (DomainValueF s t) = DomainValue s t
    embed (VarF v) = Var v
    embed (InjectionF source target t) = Injection source target t
    embed (KMapF sort conc sym) = KMap sort conc sym

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
        SymbolApplication sym [source, target] [arg]
            | sym == injectionSymbol = Injection source target arg
        SymbolApplication sym@Symbol{attributes = SymbolAttributes{isKMapSymbol = Just def}} sorts args =
            let (keyVals, rest) = internaliseKmap def $ Term mempty $ SymbolApplicationF sym sorts args
             in KMap def keyVals rest
        SymbolApplication sym sorts args =
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
                            -- Constructors and injections are evaluated if their arguments are.
                            -- Function calls are not evaluated.
                            symIsConstructor && argAttributes.isEvaluated
                        , hash =
                            Hashable.hash ("SymbolApplication" :: ByteString, sym, sorts, map (hash . getAttributes) args)
                        , isConstructorLike =
                            symIsConstructor && argAttributes.isConstructorLike
                        }
                    $ SymbolApplicationF sym sorts args

pattern DomainValue :: Sort -> ByteString -> Term
pattern DomainValue sort value <- Term _ (DomainValueF sort value)
    where
        DomainValue sort value =
            Term
                mempty
                    { hash = Hashable.hash ("DomainValue" :: ByteString, sort, value)
                    , isConstructorLike = True
                    }
                $ DomainValueF sort value

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
                        }
                    $ KMapF def (Set.toList $ Set.fromList $ keyVals ++ keyVals') rest'
{-# COMPLETE AndTerm, SymbolApplication, DomainValue, Var, Injection, KMap #-}

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
                , isKMapSymbol = Nothing
                }
        }

-- convenience patterns
pattern AndBool :: [Term] -> Term
pattern AndBool ts <-
    SymbolApplication (Symbol "Lbl'Unds'andBool'Unds'" _ _ _ _) _ ts

pattern DV :: Sort -> Symbol
pattern DV sort <- Symbol "\\dv" _ _ sort _

pattern DotDotDot :: Term
pattern DotDotDot = DomainValue (SortApp "internalDummySort" []) "..."

{- | A predicate describes constraints on terms. It will always evaluate
   to 'Top' or 'Bottom'. Notice that 'Predicate's don't have a sort.
-}
data Predicate
    = AndPredicate Predicate Predicate
    | Bottom
    | Ceil Term
    | EqualsTerm Term Term
    | EqualsPredicate Predicate Predicate
    | Exists Variable Predicate
    | Forall Variable Predicate
    | Iff Predicate Predicate
    | Implies Predicate Predicate
    | In Term Term
    | Not Predicate
    | Or Predicate Predicate
    | Top
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

makeBaseFunctor ''Predicate

--------------------

-- | A term (configuration) constrained by a number of predicates.
data Pattern = Pattern
    { term :: Term
    , constraints :: ![Predicate]
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data TermOrPredicate -- = Either Predicate Pattern
    = APredicate Predicate
    | TermAndPredicate Pattern
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

-- | Un-escapes special characters in symbol names
decodeLabel :: ByteString -> Either String ByteString
decodeLabel str
    | BS.null str = Right str
    | "'" `BS.isPrefixOf` str =
        let (encoded, rest) = BS.span (/= '\'') (BS.tail str)
         in (<>) <$> decode encoded <*> decodeLabel (BS.drop 1 rest)
    | otherwise =
        let (notEncoded, rest) = BS.span (/= '\'') str
         in (notEncoded <>) <$> decodeLabel rest
  where
    decode :: ByteString -> Either String ByteString
    decode s
        | BS.null s = Right s
        | BS.length code < 4 = Left $ "Bad character code  " <> show code
        | otherwise =
            maybe
                (Left $ "Unknown character code  " <> show code)
                (\c -> (c <>) <$> decode rest)
                (Map.lookup code decodeMap)
      where
        (code, rest) = BS.splitAt 4 s

decodeMap :: Map.Map ByteString ByteString
decodeMap =
    Map.fromList
        [ ("Spce", " ")
        , ("Bang", "!")
        , ("Quot", "\"")
        , ("Hash", "#")
        , ("Dolr", "$")
        , ("Perc", "%")
        , ("And-", "&")
        , ("Apos", "'")
        , ("LPar", "(")
        , ("RPar", ")")
        , ("Star", "*")
        , ("Plus", "+")
        , ("Comm", ",")
        , ("Hyph", "-")
        , ("Stop", ".")
        , ("Slsh", "/")
        , ("Coln", ":")
        , ("SCln", ";")
        , ("-LT-", "<")
        , ("Eqls", "=")
        , ("-GT-", ">")
        , ("Ques", "?")
        , ("-AT-", "@")
        , ("LSqB", "[")
        , ("RSqB", "]")
        , ("Bash", "\\")
        , ("Xor-", "^")
        , ("Unds", "_")
        , ("BQuo", "`")
        , ("LBra", "{")
        , ("Pipe", "|")
        , ("RBra", "}")
        , ("Tild", "~")
        ]

decodeLabel' :: ByteString -> ByteString
decodeLabel' orig =
    fromRight orig (decodeLabel orig)

-- used for printing the string as it appears (with codepoints)
prettyBS :: ByteString -> Pretty.Doc a
prettyBS = Pretty.pretty . Text.decodeUtf8

instance Pretty Term where
    pretty = \case
        AndTerm t1 t2 ->
            pretty t1 <> "/\\" <> pretty t2
        SymbolApplication (Symbol "Lbl'Unds'Set'Unds'" _ _ _ _) _ args ->
            Pretty.braces . Pretty.hsep . Pretty.punctuate Pretty.comma $ concatMap collectSet args
        SymbolApplication symbol _sortParams args ->
            pretty (Text.replace "Lbl" "" $ Text.decodeUtf8 $ decodeLabel' symbol.name)
                <> KPretty.argumentsP args
        DotDotDot -> "..."
        DomainValue _sort bs -> pretty $ show $ Text.decodeLatin1 bs
        Var var -> pretty var
        Injection _source _target t' -> pretty t'
        KMap _attrs keyVals rest ->
            Pretty.braces . Pretty.hsep . Pretty.punctuate Pretty.comma $
                [pretty k <> "->" <> pretty v | (k, v) <- keyVals]
                    ++ maybe [] ((: []) . pretty) rest
      where
        collectSet = \case
            SymbolApplication (Symbol "Lbl'Unds'Set'Unds'" _ _ _ _) _ args ->
                concatMap collectSet args
            SymbolApplication (Symbol "LblSetItem" _ _ _ _) _ args -> map pretty args
            other -> [pretty other]

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
    pretty =
        \case
            AndPredicate p1 p2 ->
                "\\andPredicate"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p1, p2]
            Bottom ->
                "\\bottom"
                    <> KPretty.noParameters
                    <> KPretty.noArguments
            Ceil t ->
                "\\ceil"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [t]
            EqualsTerm t1 t2 ->
                "\\equalsTerm"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [t1, t2]
            EqualsPredicate p1 p2 ->
                "\\equalsPredicate"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p1, p2]
            Exists v p ->
                "\\exists"
                    <> KPretty.noParameters
                    <> KPretty.arguments' [pretty v, pretty p]
            Forall v p ->
                "\\forall"
                    <> KPretty.noParameters
                    <> KPretty.arguments' [pretty v, pretty p]
            Iff p1 p2 ->
                "\\iff"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p1, p2]
            Implies p1 p2 ->
                "\\implies"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p1, p2]
            In t1 t2 ->
                "\\in"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [t1, t2]
            Not p ->
                "\\not"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p]
            Or p1 p2 ->
                "\\or"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [p1, p2]
            Top ->
                "\\top"
                    <> KPretty.noParameters
                    <> KPretty.noArguments

instance Pretty Pattern where
    pretty patt =
        Pretty.vsep $
            [ "Term:"
            , Pretty.indent 4 $ pretty patt.term
            , "Conditions:"
            ]
                <> fmap (Pretty.indent 4 . pretty) patt.constraints
