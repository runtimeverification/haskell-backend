{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Base (
    -- export everything, modules above can re-export only type names
    module Kore.Pattern.Base,
) where

import Control.DeepSeq (NFData (..))
import Data.Either (fromRight)
import Data.Functor.Foldable
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Hashable (Hashable)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics (Generic)
import Kore.Definition.Attributes.Base (
    SymbolAttributes (..),
    SymbolType (..),
 )
import Kore.Prettyprinter qualified as KPretty
import Prettyprinter (Pretty (..))
import Prettyprinter qualified as Pretty

type VarName = Text
type SymbolName = Text
type SortName = Text

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
    deriving anyclass (NFData)

data Symbol = Symbol
    { name :: SymbolName
    , sortVars :: [VarName]
    , argSorts :: [Sort]
    , resultSort :: Sort
    , attributes :: SymbolAttributes
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

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
    | DomainValueF Sort Text
    | VarF Variable
    deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

{- | Term attributes are synthetic (bottom-up) attributes that cache
   information about a term to avoid unnecessary AST
   traversals. Attributes are computed when terms are constructed (see
   patterns below).
-}
data TermAttributes = TermAttributes
    { variables :: !(Set Variable)
    , isEvaluated :: !Bool
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

instance Semigroup TermAttributes where
    a1 <> a2 =
        TermAttributes
            { variables = a1.variables <> a2.variables
            , isEvaluated = a1.isEvaluated && a2.isEvaluated
            }

instance Monoid TermAttributes where
    mempty = TermAttributes Set.empty True

-- | A term together with its attributes.
data Term = Term TermAttributes (TermF Term)
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

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

-- smart term constructors, as bidirectional patterns
pattern AndTerm :: Term -> Term -> Term
pattern AndTerm t1 t2 <- Term _ (AndTermF t1 t2)
    where
        AndTerm t1@(Term a1 _) t2@(Term a2 _) = Term (a1 <> a2) $ AndTermF t1 t2

pattern SymbolApplication :: Symbol -> [Sort] -> [Term] -> Term
pattern SymbolApplication sym sorts args <- Term _ (SymbolApplicationF sym sorts args)
    where
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
             in Term argAttributes{isEvaluated = newEvaluatedFlag} $
                    SymbolApplicationF sym sorts args

pattern DomainValue :: Sort -> Text -> Term
pattern DomainValue sort value <- Term _ (DomainValueF sort value)
    where
        DomainValue sort value = Term mempty $ DomainValueF sort value

pattern Var :: Variable -> Term
pattern Var v <- Term _ (VarF v)
    where
        Var v = Term mempty{variables = Set.singleton v} (VarF v)

{-# COMPLETE AndTerm, SymbolApplication, DomainValue, Var #-}

-- convenience patterns
pattern AndBool :: [Term] -> Term
pattern AndBool ts <-
    SymbolApplication (Symbol "Lbl'Unds'andBool'Unds'" _ _ _ _) _ ts

pattern DV :: Sort -> Symbol
pattern DV sort <- Symbol "\\dv" _ _ sort _

-- NB assumes a particular shape and order of sort variables of the
-- particular symbol "inj". A custom representation would be safer.
pattern Injection :: Sort -> Sort -> Term -> Term
pattern Injection fromSort toSort term <-
    SymbolApplication (Symbol "inj" _ _ _ _) [fromSort, toSort] [term]

{- | A predicate describes constraints on terms. It will always evaluate
   to 'Top' or 'Bottom'. Notice that 'Predicate's don't have a sort.
-}
data Predicate
    = AndPredicate Predicate Predicate
    | Bottom
    | Ceil Term
    | EqualsTerm Term Term
    | EqualsPredicate Predicate Predicate
    | Exists VarName Predicate
    | Forall VarName Predicate
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
decodeLabel :: Text -> Either String Text
decodeLabel str
    | Text.null str = Right str
    | "'" `Text.isPrefixOf` str =
        let (encoded, rest) = Text.span (/= '\'') (Text.tail str)
         in (<>) <$> decode encoded <*> decodeLabel (Text.drop 1 rest)
    | otherwise =
        let (notEncoded, rest) = Text.span (/= '\'') str
         in (notEncoded <>) <$> decodeLabel rest
  where
    decode :: Text -> Either String Text
    decode s
        | Text.null s = Right s
        | Text.length code < 4 = Left $ "Bad character code  " <> show code
        | otherwise =
            maybe
                (Left $ "Unknown character code  " <> show code)
                (\c -> (c <>) <$> decode rest)
                (Map.lookup code decodeMap)
      where
        (code, rest) = Text.splitAt 4 s

decodeMap :: Map.Map Text Text
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

decodeLabel' :: Text -> Text
decodeLabel' orig =
    fromRight orig (decodeLabel orig)

instance Pretty Term where
    pretty =
        \case
            AndTerm t1 t2 ->
                "\\andTerm"
                    <> KPretty.noParameters
                    <> KPretty.argumentsP [t1, t2]
            SymbolApplication symbol sortParams args ->
                pretty (decodeLabel' symbol.name)
                    <> KPretty.parametersP sortParams
                    <> KPretty.argumentsP args
            DomainValue sort text ->
                "\\dv"
                    <> KPretty.parametersP [sort]
                    <> KPretty.argumentsP [text]
            Var var -> pretty var

instance Pretty Sort where
    pretty (SortApp name params) =
        Pretty.pretty name <> KPretty.parametersP params
    pretty (SortVar name) =
        Pretty.pretty name

instance Pretty Variable where
    pretty var =
        Pretty.pretty (decodeLabel' var.variableName)
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
            Exists vn p ->
                "\\exists"
                    <> KPretty.noParameters
                    <> KPretty.arguments' [pretty vn, pretty p]
            Forall vn p ->
                "\\forall"
                    <> KPretty.noParameters
                    <> KPretty.arguments' [pretty vn, pretty p]
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
