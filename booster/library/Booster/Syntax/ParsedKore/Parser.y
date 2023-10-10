{
{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Internal Parser module for parsing KORE Text.
-}

module Booster.Syntax.ParsedKore.Parser (
    Parser,
    parseDefinition,
    parsePattern,
    parseModule,
    parseSentence,
    ParsedSentence(SentenceSymbol)
) where

import Data.ByteString.Lazy.Char8 qualified as B
import Data.Char qualified as Char
import Data.List (
    foldl',
    foldl1'
 )
import Data.Maybe (mapMaybe)
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Numeric.Natural

import Booster.Syntax.ParsedKore.Lexer
import Booster.Syntax.ParsedKore.LexerWrapper
import Booster.Syntax.ParsedKore.Base
import Kore.Syntax.Json.Types as Syntax

}

%name aliasHeadStart AliasHead
%name attributesStart Attributes
%name definitionStart Definition
%name elementVariableStart ElementVariable
%name idStart Id
%name moduleStart Module
%name patternStart Pattern
%name sentenceStart Sentence
%name setVariableStart SetVariable
%name sortStart Sort
%name sortsParenStart SortsParen
%name sortVariableStart SortVariable
%name sortVariablesStart SortVariables
%name stringLiteralStart StringLiteral
%name symbolHeadStart SymbolHead

%tokentype { Token }
%monad { Alex }
%lexer { alexMonadScan >>= } { Token _ TokenEOF }
%error { happyError }

%token
    module               { Token _ TokenModule }
    endmodule            { Token _ TokenEndModule }
    import               { Token _ TokenImport }
    sort                 { Token _ TokenSort }
    symbol               { Token _ TokenSymbol }
    where                { Token _ TokenWhere }
    alias                { Token _ TokenAlias }
    axiom                { Token _ TokenAxiom }
    claim                { Token _ TokenClaim }
    hookedSort           { Token _ TokenHookedSort }
    hookedSymbol         { Token _ TokenHookedSymbol }
    ':='                 { Token _ TokenColonEqual }
    ':'                  { Token _ TokenColon }
    '{'                  { Token _ TokenLeftBrace }
    '}'                  { Token _ TokenRightBrace }
    '['                  { Token _ TokenLeftBracket }
    ']'                  { Token _ TokenRightBracket }
    '('                  { Token _ TokenLeftParen }
    ')'                  { Token _ TokenRightParen }
    ','                  { Token _ TokenComma }
    top                  { Token _ TokenTop }
    bottom               { Token _ TokenBottom }
    not                  { Token _ TokenNot }
    and                  { Token _ TokenAnd }
    or                   { Token _ TokenOr }
    implies              { Token _ TokenImplies }
    iff                  { Token _ TokenIff }
    exists               { Token _ TokenExists }
    forall               { Token _ TokenForall }
    mu                   { Token _ TokenMu }
    nu                   { Token _ TokenNu }
    ceil                 { Token _ TokenCeil }
    floor                { Token _ TokenFloor }
    equals               { Token _ TokenEquals }
    in                   { Token _ TokenIn }
    next                 { Token _ TokenNext }
    rewrites             { Token _ TokenRewrites }
    dv                   { Token _ TokenDomainValue }
    leftAssoc            { Token _ TokenLeftAssoc }
    rightAssoc           { Token _ TokenRightAssoc }
    ident                { Token _ (TokenIdent _) }
    setIdent             { Token _ (TokenSetIdent _) }
    string               { Token _ (TokenString $$) }

%%

Definition :: { ParsedDefinition }
            : Attributes Modules { ParsedDefinition (reverse $2) $1 }

Attributes :: { ParsedAttributes }
	    : '[' ']' { [] }
            | '[' AttributeList ']' { reverse $2 }

AttributeList :: {[(AttributeName, AttributeValue)]}
	    : Pattern { [ attributeFromPattern $1] }
            | AttributeList ',' Pattern { attributeFromPattern $3 : $1 }

Modules :: {[ParsedModule]}
         : Module { [$1] }
         | Modules Module { $2 : $1 }

Module :: {ParsedModule}
        : module ident Sentences endmodule Attributes
          { mkModule (mkId $2) $5 $3 }
        | module ident endmodule Attributes
          { mkModule (mkId $2) $4 [] }

Sentences :: {[ParsedSentence]}
	   : Sentence { [$1] }
           | Sentences Sentence { $2 : $1 }

Sentence :: {ParsedSentence}
	  : import ident Attributes
            { SentenceImport (mkId $2, $3) }
          | sort Id SortVariables Attributes
            { SentenceSort ParsedSort{name=$2, sortVars=$3, isHooked=False, attributes=$4} }
          | hookedSort Id SortVariables Attributes
            { SentenceSort ParsedSort{name=$2, sortVars=$3, isHooked=True, attributes=$4} }
          | symbol SymbolHead SortsParen ':' Sort Attributes
            { SentenceSymbol ($2 $3 $5 False $6) }
          | hookedSymbol SymbolHead SortsParen ':' Sort Attributes
            { SentenceSymbol ($2 $3 $5 True $6) }
          | alias AliasHead SortsParen ':' Sort where Application ':=' Pattern Attributes
            { SentenceAlias $2 $3 $5 $7 $9 $10 }
          | axiom SortVariables Pattern Attributes
            { SentenceAxiom ParsedAxiom{axiom=$3, sortVars=$2, attributes=$4} }
          | claim SortVariables Pattern Attributes
            { SentenceClaim {- ParsedClaim ParsedAxiom{axiom=$2, sortVars=$3, attributes=$4} -} }

Id :: { Id }
    : ident { mkId $1 }

AliasHead :: { ParsedAliasHead }
	   : Id SortVariables { ParsedAliasHead $1 $2 }

SymbolHead :: { [Sort] -> Sort -> Bool -> ParsedAttributes -> ParsedSymbol }
	    : Id SortVariables { ParsedSymbol $1 $2 }

SortVariables :: { [Id] }
	       : '{' SortVariableList '}' { reverse $2 }
               | '{' '}' { [] }

SortVariableList :: { [Id] }
		  : SortVariable { [$1] }
                  | SortVariableList ',' SortVariable { $3 : $1 }

SortVariable :: { Id }
	      : Id { $1 }

SortsParen :: { [Sort] }
       : '(' SortList ')' { reverse $2 }
       | '(' ')' { [] }

SortsBrace :: { [Sort] }
	    : '{' SortList '}' { reverse $2 }
            | '{' '}' { [] }

SortList :: { [Sort] }
	  : Sort { [$1] }
          | SortList ',' Sort { $3 : $1 }

Sort :: { Sort }
      : Id { SortVar $1 }
    | Id SortsBrace { SortApp $1 $2 }

Pattern :: { KorePattern }
	 : ElementVariable { uncurry KJEVar $1 }
	 | SetVariable { uncurry KJSVar $1 }
         | ApplicationPattern { $1 }
         | StringLiteralPattern { $1 }

ElementVariable :: { (Id, Sort) }
	         : ident ':' Sort { (mkId $1, $3) }
SetVariable :: { (Id, Sort) }
	     : setIdent ':' Sort { (mkId $1, $3) }
SomeVariable :: { KorePattern }
	      : ident ':' Sort { KJEVar (mkId $1) $3 }
	      | setIdent ':' Sort { KJSVar (mkId $1) $3 }

StringLiteralPattern :: { KorePattern }
		      : StringLiteral { KJString $1 }

StringLiteral :: { Text }
               : string { $1 }

ApplicationPattern :: { KorePattern }
		    : leftAssoc '{' '}' '(' ident SortsBrace NePatterns ')'
                      { mkAssoc True $5 $6 $7 }
		    | leftAssoc '{' '}' '(' and SortsBrace NePatterns ')'
                      { mkAssoc True $5 $6 $7 }
		    | leftAssoc '{' '}' '(' or SortsBrace NePatterns ')'
                      { mkAssoc True $5 $6 $7 }
		    | leftAssoc '{' '}' '(' implies SortsBrace NePatterns ')'
                      { mkAssoc True $5 $6 $7 }
		    | leftAssoc '{' '}' '(' iff SortsBrace NePatterns ')'
                      { mkAssoc True $5 $6 $7 }
                    | rightAssoc '{' '}' '(' ident SortsBrace NePatterns ')'
                      { mkAssoc False $5 $6 $7 }
                    | rightAssoc '{' '}' '(' and SortsBrace NePatterns ')'
                      { mkAssoc False $5 $6 $7 }
                    | rightAssoc '{' '}' '(' or SortsBrace NePatterns ')'
                      { mkAssoc False $5 $6 $7 }
                    | rightAssoc '{' '}' '(' implies SortsBrace NePatterns ')'
                      { mkAssoc False $5 $6 $7 }
                    | rightAssoc '{' '}' '(' iff SortsBrace NePatterns ')'
                      { mkAssoc False $5 $6 $7 }
                    | top '{' Sort '}' '(' ')'
                      { KJTop {sort = $3} }
                    | bottom '{' Sort '}' '(' ')'
                      { KJBottom {sort = $3} }
                    | not '{' Sort '}' '(' Pattern ')'
                      { KJNot{sort = $3, arg = $6} }
                    | and '{' Sort '}' Patterns
                      { mkAnd $3 $5 }
                    | or '{' Sort '}' Patterns
                      { mkOr $3 $5 }
                    | implies '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { KJImplies{sort = $3, first = $6, second = $8} }
                    | iff '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { KJIff{sort = $3, first = $6, second = $8} }
                    | exists '{' Sort '}' '(' ElementVariable ',' Pattern ')'
                      { KJExists{sort = $3, var = fst $6, varSort = snd $6, arg = $8} }
                    | forall '{' Sort '}' '(' ElementVariable ',' Pattern ')'
                      { KJForall{sort = $3, var = fst $6, varSort = snd $6, arg = $8} }
                    | mu '{' '}' '(' SetVariable ',' Pattern ')'
                      { KJMu{var = fst $5, varSort = snd $5, arg = $7} }
                    | nu '{' '}' '(' SetVariable ',' Pattern ')'
                      { KJNu{var = fst $5, varSort = snd $5, arg = $7} }
                    | ceil '{' Sort ',' Sort '}' '(' Pattern ')'
                      { KJCeil{argSort = $3, sort = $5, arg = $8} }
                    | floor '{' Sort ',' Sort '}' '(' Pattern ')'
                      { KJFloor{argSort = $3, sort = $5, arg = $8} }
                    | equals '{' Sort ',' Sort '}' '(' Pattern ',' Pattern ')'
                      { KJEquals{argSort = $3, sort = $5, first = $8, second = $10} }
                    | in '{' Sort ',' Sort '}' '(' Pattern ',' Pattern ')'
                      { KJIn{argSort = $3, sort = $5, first = $8, second = $10} }
                    | next '{' Sort '}' '(' Pattern ')'
                      { KJNext{ sort = $3, dest = $6} }
                    | rewrites '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { KJRewrites{sort = $3, source = $6, dest = $8} }
                    | dv '{' Sort '}' '(' StringLiteral')'
                      { KJDV{sort = $3, value = $6} }
                    | Id SortsBrace Patterns
                      { KJApp{name = $1, sorts = $2, args = $3} }

Application :: { AliasApp }
	     : Id SortsBrace SomeVariables { AliasApp $1 $2 $3 }

SomeVariables :: { [KorePattern] }
	       : '(' SomeVariableList ')' { reverse $2 }
               | '(' ')' { [] }

SomeVariableList :: { [KorePattern] }
		  : SomeVariable { [$1] }
                  | SomeVariableList ',' SomeVariable { $3 : $1 }

Patterns :: { [KorePattern] }
	  : NePatterns { $1 }
          | '(' ')' { [] }

NePatterns :: { [KorePattern] }
	    : '(' PatternList ')' { reverse $2 }

PatternList :: { [KorePattern] }
             : Pattern { [$1] }
	     | PatternList ',' Pattern { $3 : $1 }

{

data AliasApp = AliasApp Id [Sort] [KorePattern]
    deriving (Eq, Show)

data ParsedAliasHead = ParsedAliasHead Syntax.Id [Syntax.Id]
    deriving (Eq, Show)

-- | helpers for parsing module components
data ParsedSentence
    = SentenceImport (Syntax.Id, ParsedAttributes)
    | SentenceSort ParsedSort
    | SentenceSymbol ParsedSymbol
    | SentenceAlias ParsedAliasHead [Sort] Sort AliasApp KorePattern ParsedAttributes
    | SentenceAxiom ParsedAxiom
    | SentenceClaim -- ParsedClaim
    deriving (Eq, Show)

mkModule :: Syntax.Id -> ParsedAttributes -> [ParsedSentence] -> ParsedModule
mkModule name attributes sentences
--     = ParsedModule {name, imports, sorts, symbols, aliases, axioms, claims, attributes}
    = ParsedModule {name, imports, sorts, symbols, axioms, aliases, attributes}
  where
    (imports, sorts, symbols, axioms, aliases) = foldl' collect ([], [], [], [], []) sentences
    -- intentionally reversing the list
    collect ::
        ([(Syntax.Id, ParsedAttributes)], [ParsedSort], [ParsedSymbol], [ParsedAxiom], [ParsedAlias]) ->
        ParsedSentence ->
        ([(Syntax.Id, ParsedAttributes)], [ParsedSort], [ParsedSymbol], [ParsedAxiom], [ParsedAlias])
    collect acc@(!imports, !sorts, !symbols, !axioms, !aliases) = \case
        SentenceImport id -> (id:imports, sorts, symbols, axioms, aliases)
        SentenceSort s -> (imports, s:sorts, symbols, axioms, aliases)
        SentenceSymbol s -> (imports, sorts, s:symbols, axioms, aliases)
        SentenceAxiom a -> (imports, sorts, symbols, a:axioms, aliases)
        SentenceAlias aliasHead argSorts resSort aliasApp rhs attributes ->
            let a = mkParsedAlias aliasHead argSorts resSort aliasApp rhs attributes
             in (imports, sorts, symbols, axioms, a:aliases)
        _other -> acc

mkParsedAlias ::
    ParsedAliasHead ->
    [Sort] ->
    Sort ->
    AliasApp ->
    KorePattern ->
    ParsedAttributes ->
    ParsedAlias
mkParsedAlias
    (ParsedAliasHead name sortVars)
    argSorts
    sort
    (AliasApp appName appSortVars pattArgs)
    rhs
    attributes
    | name /= appName =
        error ("Alias declaration inconsistency: " <> show name <> " is different from " <> show appName)
    | Just appSortVarIds <- traverse retractSortVariable appSortVars
    , sortVars /= appSortVarIds =
        error ("Alias declaration inconsistency: " <> show sortVars <> " is different from " <> show appSortVarIds <> " in declaration for " <> show name)
    | Just args <- traverse retractVariable pattArgs =
        ParsedAlias
            { name
            , sortVars
            , argSorts
            , sort
            , args
            , rhs
            , attributes
            }
    | otherwise =
        error ("Alias " <> show name <> " should only have variables as arguments.")
  where
    retractVariable :: Syntax.KorePattern -> Maybe Syntax.Id
    retractVariable Syntax.KJEVar{name} = Just name
    retractVariable Syntax.KJSVar{name} = Just name
    retractVariable _ = Nothing

    retractSortVariable :: Syntax.Sort -> Maybe Syntax.Id
    retractSortVariable Syntax.SortVar{name} = Just name
    retractSortVariable _ = Nothing

-- helper to parse attributes
attributeFromPattern :: KorePattern -> (AttributeName, AttributeValue)
attributeFromPattern KJApp {name, sorts = [], args = []}
    = (name, [])
attributeFromPattern KJApp {name, sorts = [], args = [KJString{value}]}
    = (name, [value])
-- attributes of AC structure sorts have this shape
attributeFromPattern KJApp {name, sorts = [], args = [KJApp{name = Syntax.Id name2, args = []}]}
    = (name, [name2])
-- priorities attribute or concrete/symbolic has this shape
attributeFromPattern KJApp {name, sorts = [], args}
    = (name, asTextList args)
-- The subsort attribute information is given in the sort field
attributeFromPattern KJApp {name, sorts = [SortApp{name = Syntax.Id s1}, SortApp{name = Syntax.Id s2}], args = []}
    = (name, [s1 <> " < " <> s2])
attributeFromPattern badPat
    = error $ "Unexpected attribute shape: " <> show badPat

-- extract attributes from patterns used for attributes
asText :: KorePattern -> [Text]
asText KJString{value} = [value]
asText KJApp{name = Syntax.Id n, sorts = [], args = []} = [n]
asText KJEVar{name = Syntax.Id n, sort = SortApp{name = Syntax.Id s}} = [n <> ":" <> s]
asText other = []  -- HACK

asTextList :: [KorePattern] -> [Text]
asTextList = concatMap asText


{- | Expand a \\left-assoc or \\right-assoc directive into a ParsedPattern. First
argument is True for \\left-assoc and False for \\right-assoc.
-}
mkAssoc :: Bool -> Token -> [Sort] -> [KorePattern] -> KorePattern
mkAssoc True id sorts ps = foldl1' (mkApply id sorts) ps
mkAssoc False id sorts ps = foldr1 (mkApply id sorts) ps

mkAnd :: Sort -> [KorePattern] -> KorePattern
mkAnd s [] = KJTop s
mkAnd s [p] = p
mkAnd s ps = KJAnd s ps

mkOr :: Sort -> [KorePattern] -> KorePattern
mkOr s [] = KJBottom s
mkOr s [p] = p
mkOr s ps = KJOr s ps

{- | Helper function to expand a \\left-assoc or \\right-assoc directive for
a particular type of pattern. Only implemented for Application patterns and
built-in patterns with one sort parameter and two children of the same sort as
the result. Namely, \\and, \\or, \\implies, and \\iff. Designed to be passed to
foldl1' or foldr1.
-}
mkApply :: Token -> [Sort] -> KorePattern -> KorePattern -> KorePattern
mkApply tok [sort] first second
    | Token _ TokenAnd <- tok = KJAnd sort [first, second]
    | Token _ TokenOr <- tok = KJOr sort [first, second]
    | Token _ TokenImplies <- tok = KJImplies sort first second
    | Token _ TokenIff <- tok = KJIff sort first second
mkApply tok sorts@[_, _] first second
    | Token _ (TokenIdent _) <- tok = KJApp (mkId tok) sorts [first, second]
mkApply other _ _ _ = error $ "mkApply: unsupported token " <> show other

{- | Create an Id from a Token. Uses current location of that Token to create
an AstLocation.
-}
mkId :: Token -> Id
mkId tok@(Token (AlexPn fileName _ line column) _) =
    Id $ getIdentName tok

--

type Parser a = FilePath -> Text -> Either String a

{- | Helper function for parsing a particular NonTerminal in the grammar. The
function specified by the %name directive for that NonTerminal should be passed
as the first argument to the function. -}
parseNonTerminal :: Alex a -> Parser a
parseNonTerminal a fp s = runAlex fp (Text.encodeUtf8 s) a

-- Functions for parsing specific NonTerminals.

parseAliasHead :: Parser ParsedAliasHead
parseAliasHead = parseNonTerminal aliasHeadStart

parseAttributes :: Parser ParsedAttributes
parseAttributes = parseNonTerminal attributesStart

parseDefinition :: Parser ParsedDefinition
parseDefinition = parseNonTerminal definitionStart

parseElementVariable :: Parser (Id, Sort)
parseElementVariable = parseNonTerminal elementVariableStart

parseId :: Parser Id
parseId = parseNonTerminal idStart

parseModule :: Parser ParsedModule
parseModule = parseNonTerminal moduleStart

parsePattern :: Parser KorePattern
parsePattern = parseNonTerminal patternStart

parseSentence :: Parser ParsedSentence
parseSentence = parseNonTerminal sentenceStart

parseSetVariable :: Parser (Id, Sort)
parseSetVariable = parseNonTerminal setVariableStart

parseSort :: Parser Sort
parseSort = parseNonTerminal sortStart

parseSortsParen :: Parser [Sort]
parseSortsParen = parseNonTerminal sortsParenStart

parseSortVariable :: Parser Id
parseSortVariable = parseNonTerminal sortVariableStart

parseSortVariables :: Parser [Id]
parseSortVariables = parseNonTerminal sortVariablesStart

parseStringLiteral :: Parser Text
parseStringLiteral = parseNonTerminal stringLiteralStart

parseSymbolHead :: Parser ([Sort] -> Sort -> Bool -> ParsedAttributes -> ParsedSymbol)
parseSymbolHead = parseNonTerminal symbolHeadStart

{- | Reports a parsing error if parsing fails. Called by code generated by
Happy.
-}
happyError :: Token -> Alex a
happyError (Token (AlexPn fp _ line column) t) =
    alexError fp line column ("unexpected token " ++ (show t))

}
