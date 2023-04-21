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
    SymbolAttributes (..),
    SymbolType (..),
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
    , hash :: !Int
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

instance Semigroup TermAttributes where
    a1 <> a2 =
        TermAttributes
            { variables = a1.variables <> a2.variables
            , isEvaluated = a1.isEvaluated && a2.isEvaluated
            , hash = 0
            }

instance Monoid TermAttributes where
    mempty = TermAttributes Set.empty True 0

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

instance Corecursive Term where
    embed (AndTermF t1 t2) = AndTerm t1 t2
    embed (SymbolApplicationF s ss ts) = SymbolApplication s ss ts
    embed (DomainValueF s t) = DomainValue s t
    embed (VarF v) = Var v
    embed (InjectionF source target t) = Injection source target t

-- smart term constructors, as bidirectional patterns
pattern AndTerm :: Term -> Term -> Term
pattern AndTerm t1 t2 <- Term _ (AndTermF t1 t2)
    where
        AndTerm t1@(Term a1 _) t2@(Term a2 _) =
            Term
                (a1 <> a2)
                    { hash = Hashable.hash ("AndTerm" :: ByteString, hash a1, hash a2)
                    }
                $ AndTermF t1 t2

pattern SymbolApplication :: Symbol -> [Sort] -> [Term] -> Term
pattern SymbolApplication sym sorts args <- Term _ (SymbolApplicationF sym sorts args)
    where
        SymbolApplication sym [source, target] [arg]
            | sym == injectionSymbol = Injection source target arg
        SymbolApplication sym sorts args =
            let argAttributes = mconcat $ map getAttributes args
                newEvaluatedFlag =
                    case sym.attributes.symbolType of
                        -- constructors and injections are evaluated if their arguments are
                        Constructor -> argAttributes.isEvaluated
                        SortInjection -> argAttributes.isEvaluated
                        -- function calls are not evaluated
                        PartialFunction -> False
                        TotalFunction -> False
             in Term
                    argAttributes
                        { isEvaluated = newEvaluatedFlag
                        , hash = Hashable.hash ("SymbolApplication" :: ByteString, sym, sorts, map (hash . getAttributes) args)
                        }
                    $ SymbolApplicationF sym sorts args

pattern DomainValue :: Sort -> ByteString -> Term
pattern DomainValue sort value <- Term _ (DomainValueF sort value)
    where
        DomainValue sort value =
            Term
                mempty
                    { hash = Hashable.hash ("DomainValue" :: ByteString, sort, value)
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

{-# COMPLETE AndTerm, SymbolApplication, DomainValue, Var, Injection #-}

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
    pretty =
        \case
            AndTerm t1 t2 ->
                "\\andTerm"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [t1, t2]
            SymbolApplication symbol sortParams args ->
                prettyBS (decodeLabel' symbol.name)
                    <> KPretty.parametersP sortParams
                    <> KPretty.argumentsP args
            DomainValue sort bs ->
                "\\dv"
                    <> KPretty.parametersP [sort]
                    -- prints the bytes of the string as data
                    <> KPretty.argumentsP [show $ Text.decodeLatin1 bs]
            Var var -> pretty var
            Injection source target t ->
                "\\inj"
                    <> KPretty.parametersP [source, target]
                    <> KPretty.argumentsP [t]

newtype PrettyTerm = PrettyTerm Term

instance Pretty PrettyTerm where
    pretty (PrettyTerm t) = case t of
        AndTerm t1 t2 ->
            pretty (PrettyTerm t1) <> "/\\" <> pretty (PrettyTerm t2)
        SymbolApplication (Symbol "Lbl'Unds'Set'Unds'" _ _ _ _) _ args ->
            Pretty.braces . Pretty.hsep . Pretty.punctuate Pretty.comma $ concatMap collectSet args
        SymbolApplication symbol _sortParams args ->
            pretty (Text.replace "Lbl" "" $ Text.decodeUtf8 $ decodeLabel' symbol.name)
                <> KPretty.argumentsP (map PrettyTerm args)
        DotDotDot -> "..."
        DomainValue _sort bs -> pretty $ show $ Text.decodeLatin1 bs
        Var var -> pretty var
        Injection _source _target t' -> pretty $ PrettyTerm t'
      where
        collectSet = \case
            SymbolApplication (Symbol "Lbl'Unds'Set'Unds'" _ _ _ _) _ args ->
                concatMap collectSet args
            SymbolApplication (Symbol "LblSetItem" _ _ _ _) _ args -> map (pretty . PrettyTerm) args
            other -> [pretty $ PrettyTerm other]

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
