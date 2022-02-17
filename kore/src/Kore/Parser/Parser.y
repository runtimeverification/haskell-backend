{
{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Internal Parser module for parsing KORE Text. Do not import this module
directly. Instead, import Kore.Parser.
-}

module Kore.Parser.Parser (
    embedParsedPattern,
    parseAliasHead,
    parseAttributes,
    parseDefinition,
    parseElementVariable,
    parseId,
    parseModule,
    parsePattern,
    parseSentence,
    parseSetVariable,
    parseSort,
    parseSortsParen,
    parseSortVariable,
    parseSortVariables,
    parseStringLiteral,
    parseSymbolHead,
    parseVariableCounter,
) where

import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Char as Char
import qualified Data.Functor.Foldable as Recursive
import Data.List (
    foldl1',
 )
import Data.Sup
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Kore.Attribute.Attributes
import qualified Kore.Attribute.Null as Attribute
import Kore.Syntax hiding (
    mkVariableName,
 )
import Kore.Syntax.Definition
import Kore.Syntax.Sentence
import Kore.Parser.Lexer
import Kore.Parser.LexerWrapper
import Numeric.Natural
import qualified Prelude as Prelude
import Prelude.Kore

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
    string               { Token _ (TokenString _) }

%%

Definition :: {ParsedDefinition}
            : Attributes Modules { Definition $1 (reverse $2) }

Attributes :: {Attributes}
	    : '[' ']' { Attributes [] }
            | '[' AttributeList ']' { Attributes (reverse $2) }

AttributeList :: {[ParsedPattern]}
	    : Pattern { [$1] }
            | AttributeList ',' Pattern { $3 : $1 }

Modules :: {[ParsedModule]}
         : Module { [$1] }
         | Modules Module { $2 : $1 }

Module :: {ParsedModule}
        : module ident Sentences endmodule Attributes
          { Module (ModuleName (getTokenBody $2)) (reverse $3) $5 }
        | module ident endmodule Attributes
          { Module (ModuleName (getTokenBody $2)) [] $4 }

Sentences :: {[ParsedSentence]}
	   : Sentence { [$1] }
           | Sentences Sentence { $2 : $1 }

Sentence :: {ParsedSentence}
	  : import ident Attributes
            { SentenceImportSentence (SentenceImport (ModuleName $ getTokenBody $2) $3) }
          | sort Id SortVariables Attributes
            { SentenceSortSentence (SentenceSort $2 $3 $4) }
          | hookedSort Id SortVariables Attributes
            { SentenceHookSentence (SentenceHookedSort (SentenceSort $2 $3 $4)) }
          | symbol SymbolHead SortsParen ':' Sort Attributes
            { SentenceSymbolSentence (SentenceSymbol $2 $3 $5 $6) }
          | hookedSymbol SymbolHead SortsParen ':' Sort Attributes
            { SentenceHookSentence (SentenceHookedSymbol (SentenceSymbol $2 $3 $5 $6)) }
          | alias AliasHead SortsParen ':' Sort where Application ':=' Pattern Attributes
            { SentenceAliasSentence (SentenceAlias $2 $3 $5 $7 $9 $10) }
          | axiom SortVariables Pattern Attributes
            { SentenceAxiomSentence (SentenceAxiom $2 $3 $4) }
          | claim SortVariables Pattern Attributes
            { SentenceClaimSentence (SentenceClaim (SentenceAxiom $2 $3 $4)) }

Id :: {Id}
    : ident { mkId $1 }

AliasHead :: {Alias}
	   : Id SortVariables { Alias $1 $2 }

SymbolHead :: {Symbol}
	    : Id SortVariables { Symbol $1 $2 }
	
SortVariables :: {[SortVariable]}
	       : '{' SortVariableList '}' { reverse $2 }
               | '{' '}' { [] }

SortVariableList :: {[SortVariable]}
		  : SortVariable { [$1] }
                  | SortVariableList ',' SortVariable { $3 : $1 }

SortVariable :: {SortVariable}
	      : Id { SortVariable $1 }

SortsParen :: {[Sort]}
       : '(' SortList ')' { reverse $2 }
       | '(' ')' { [] }

SortsBrace :: {[Sort]}
	    : '{' SortList '}' { reverse $2 }
            | '{' '}' { [] }

SortList :: {[Sort]}
	  : Sort { [$1] }
          | SortList ',' Sort { $3 : $1 }

Sort :: {Sort}
      : Id { SortVariableSort (SortVariable $1) }
      | Id SortsBrace { SortActualSort (SortActual $1 $2 ) }

Pattern :: {ParsedPattern}
	 : SomeVariable { embedParsedPattern $ VariableF $ Const $1 }
         | ApplicationPattern { $1 }
         | StringLiteralPattern { $1 }

ElementVariable :: {Variable (ElementVariableName VariableName)}
	         : ident ':' Sort { Variable{variableName = ElementVariableName{unElementVariableName = mkVariableName $1}, variableSort = $3} }
SetVariable :: {Variable (SetVariableName VariableName)}
	     : setIdent ':' Sort { Variable{variableName = SetVariableName{unSetVariableName = mkVariableName $1}, variableSort = $3} }
SomeVariable :: {Variable (SomeVariableName VariableName)}
	      : ident ':' Sort { Variable{variableName = SomeVariableNameElement (ElementVariableName {unElementVariableName = mkVariableName $1}), variableSort = $3} }
	      | setIdent ':' Sort { Variable{variableName = SomeVariableNameSet (SetVariableName {unSetVariableName = mkVariableName $1}), variableSort = $3} }

StringLiteralPattern :: {ParsedPattern}
		      : StringLiteral { embedParsedPattern $ StringLiteralF $ Const $1 }

StringLiteral :: {StringLiteral}
               : string { StringLiteral{getStringLiteral = getTokenBody $1} }

ApplicationPattern :: {ParsedPattern}
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
                      { embedParsedPattern $ TopF Top{topSort = $3} }
                    | bottom '{' Sort '}' '(' ')'
                      { embedParsedPattern $ BottomF Bottom{bottomSort = $3} }
                    | not '{' Sort '}' '(' Pattern ')'
                      { embedParsedPattern $ NotF Not{notSort = $3, notChild = $6} }
                    | and '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ AndF And{andSort = $3, andFirst = $6, andSecond = $8} }
                    | or '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ OrF Or{orSort = $3, orFirst = $6, orSecond = $8} }
                    | implies '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ ImpliesF Implies{impliesSort = $3, impliesFirst = $6, impliesSecond = $8} }
                    | iff '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ IffF Iff{iffSort = $3, iffFirst = $6, iffSecond = $8} }
                    | exists '{' Sort '}' '(' ElementVariable ',' Pattern ')'
                      { embedParsedPattern $ ExistsF Exists{existsSort = $3, existsVariable = $6, existsChild = $8} }
                    | forall '{' Sort '}' '(' ElementVariable ',' Pattern ')'
                      { embedParsedPattern $ ForallF Forall{forallSort = $3, forallVariable = $6, forallChild = $8} }
                    | mu '{' '}' '(' SetVariable ',' Pattern ')'
                      { embedParsedPattern $ MuF Mu{muVariable = $5, muChild = $7} }
                    | nu '{' '}' '(' SetVariable ',' Pattern ')'
                      { embedParsedPattern $ NuF Nu{nuVariable = $5, nuChild = $7} }
                    | ceil '{' Sort ',' Sort '}' '(' Pattern ')'
                      { embedParsedPattern $ CeilF Ceil{ceilOperandSort = $3, ceilResultSort = $5, ceilChild = $8} }
                    | floor '{' Sort ',' Sort '}' '(' Pattern ')'
                      { embedParsedPattern $ FloorF Floor{floorOperandSort = $3, floorResultSort = $5, floorChild = $8} }
                    | equals '{' Sort ',' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ EqualsF Equals{equalsOperandSort = $3, equalsResultSort = $5, equalsFirst = $8, equalsSecond = $10} }
                    | in '{' Sort ',' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ InF In{inOperandSort = $3, inResultSort = $5, inContainedChild = $8, inContainingChild = $10} }
                    | next '{' Sort '}' '(' Pattern ')'
                      { embedParsedPattern $ NextF Next{nextSort = $3, nextChild = $6} }
                    | rewrites '{' Sort '}' '(' Pattern ',' Pattern ')'
                      { embedParsedPattern $ RewritesF Rewrites{rewritesSort = $3, rewritesFirst = $6, rewritesSecond = $8} }
                    | dv '{' Sort '}' '(' StringLiteralPattern ')'
                      { embedParsedPattern $ DomainValueF DomainValue{domainValueSort = $3, domainValueChild = $6} }
                    | Id SortsBrace Patterns
                      { embedParsedPattern $ ApplicationF Application{applicationSymbolOrAlias = SymbolOrAlias{symbolOrAliasConstructor = $1, symbolOrAliasParams = $2}, applicationChildren = $3} }

Application :: {Application SymbolOrAlias (SomeVariable VariableName)}
	     : Id SortsBrace SomeVariables { Application{applicationSymbolOrAlias = SymbolOrAlias{symbolOrAliasConstructor = $1, symbolOrAliasParams = $2}, applicationChildren = $3} }

SomeVariables :: {[SomeVariable VariableName]}
	       : '(' SomeVariableList ')' { reverse $2 }
               | '(' ')' { [] }

SomeVariableList :: {[SomeVariable VariableName]}
		  : SomeVariable { [$1] }
                  | SomeVariableList ',' SomeVariable { $3 : $1 }

Patterns :: {[ParsedPattern]}
	  : NePatterns { $1 }
          | '(' ')' { [] }

NePatterns :: {[ParsedPattern]}
	    : '(' PatternList ')' { reverse $2 }

PatternList :: {[ParsedPattern]}
             : Pattern { [$1] }
	     | PatternList ',' Pattern { $3 : $1 }

{

{- | Helper function for parsing a particular NonTerminal in the grammar. The
function specified by the %name directive for that NonTerminal should be passed
as the first argument to the function. -}
parseNonTerminal :: Alex a -> FilePath -> Text -> Either String a
parseNonTerminal a fp s = runAlex fp (Text.encodeUtf8 s) a

-- Functions for parsing specific NonTerminals.

parseAliasHead :: FilePath -> Text -> Either String Alias
parseAliasHead = parseNonTerminal aliasHeadStart

parseAttributes :: FilePath -> Text -> Either String Attributes
parseAttributes = parseNonTerminal attributesStart

parseDefinition :: FilePath -> Text -> Either String ParsedDefinition
parseDefinition = parseNonTerminal definitionStart

parseElementVariable ::
    FilePath ->
    Text ->
    Either String (Variable (ElementVariableName VariableName))
parseElementVariable = parseNonTerminal elementVariableStart

parseId :: FilePath -> Text -> Either String Id
parseId = parseNonTerminal idStart

parseModule :: FilePath -> Text -> Either String ParsedModule
parseModule = parseNonTerminal moduleStart

parsePattern :: FilePath -> Text -> Either String ParsedPattern
parsePattern = parseNonTerminal patternStart

parseSentence :: FilePath -> Text -> Either String ParsedSentence
parseSentence = parseNonTerminal sentenceStart

parseSetVariable :: FilePath -> Text -> Either String (Variable (SetVariableName VariableName))
parseSetVariable = parseNonTerminal setVariableStart

parseSort :: FilePath -> Text -> Either String Sort
parseSort = parseNonTerminal sortStart

parseSortsParen :: FilePath -> Text -> Either String [Sort]
parseSortsParen = parseNonTerminal sortsParenStart

parseSortVariable :: FilePath -> Text -> Either String SortVariable
parseSortVariable = parseNonTerminal sortVariableStart

parseSortVariables :: FilePath -> Text -> Either String [SortVariable]
parseSortVariables = parseNonTerminal sortVariablesStart

parseStringLiteral :: FilePath -> Text -> Either String StringLiteral
parseStringLiteral = parseNonTerminal stringLiteralStart

parseSymbolHead :: FilePath -> Text -> Either String Symbol
parseSymbolHead = parseNonTerminal symbolHeadStart

{- | Reports a parsing error if parsing fails. Called by code generated by
Happy.
-}
happyError :: Token -> Alex a
happyError (Token (AlexPn fp _ line column) t) =
    alexError fp line column ("unexpected token " ++ (show t))

{-
Uses 'parseVariableCounter' to get the 'counter' for the 'Id', if any. Creates
a VariableName.
-}
getVariableName :: Id -> VariableName
getVariableName identifier =
    let (base, counter) = parseVariableCounter identifier
     in VariableName{base, counter}

-- | Read the fresh name counter (if any) from the end of an 'Id'.
parseVariableCounter :: Id -> (Id, Maybe (Sup Natural))
parseVariableCounter identifier@Id{getId, idLocation}
    -- Cases:
    -- suffix is empty: no counter, Id is not changed
    | Text.null suffix = (identifier, Nothing)
    -- suffix is all zeros: counter is zero, Id has final zero stripped
    | Text.null nonZeros =
        ( Id{idLocation, getId = base <> Text.init zeros}
        , Just (Element 0)
        )
    -- suffix is some zeros followed by non-zeros:
    --   read the counter from the non-zeros, Id is base + zeros
    | otherwise =
        ( Id{idLocation, getId = base <> zeros}
        , (Just . Element) (read $ Text.unpack nonZeros)
        )
  where
    base = Text.dropWhileEnd Char.isDigit getId
    suffix = Text.drop (Text.length base) getId
    zeros = Text.takeWhile (== '0') suffix
    nonZeros = Text.drop (Text.length zeros) suffix

-- | Construct a ParsedPattern from its indivdiual operands.
embedParsedPattern :: (PatternF VariableName) ParsedPattern -> ParsedPattern
embedParsedPattern patternBase = asPattern (mempty :< patternBase)

{- | Create an Id from a Token. Uses current location of that Token to create
an AstLocation.
-}
mkId :: Token -> Id
mkId tok@(Token (AlexPn fileName _ line column) _) =
    Id { getId = getTokenBody tok
       , idLocation = AstLocationFile $ FileLocation{fileName, line, column}
       }

-- | Create a VariableName from a Token by using mkId and getVariableName.
mkVariableName :: Token -> VariableName
mkVariableName = getVariableName . mkId

{- | Expand a \left-assoc or \right-assoc directive into a ParsedPattern. First
argument is True for \left-assoc and False for \right-assoc.
-}
mkAssoc :: Bool -> Token -> [Sort] -> [ParsedPattern] -> ParsedPattern
mkAssoc True id sorts ps = foldl1' (mkApply id sorts) ps
mkAssoc False id sorts ps = foldr1 (mkApply id sorts) ps

{- | Helper function to expand a \\left-assoc or \\right-assoc directive for
a particular type of pattern. Only implemented for Application patterns and
built-in patterns with one sort parameter and two children of the same sort as
the result. Namely, \\and, \\or, \\implies, and \\iff. Designed to be passed to
foldl1' or foldr1.
-}
mkApply :: Token -> [Sort] -> ParsedPattern -> ParsedPattern -> ParsedPattern
mkApply tok@(Token _ TokenAnd) [andSort] andFirst andSecond =
    embedParsedPattern $ AndF And{andSort, andFirst, andSecond}
mkApply tok@(Token _ TokenOr) [orSort] orFirst orSecond =
    embedParsedPattern $ OrF Or{orSort, orFirst, orSecond}
mkApply tok@(Token _ TokenImplies) [impliesSort] impliesFirst impliesSecond =
    embedParsedPattern $ ImpliesF Implies{impliesSort, impliesFirst, impliesSecond}
mkApply tok@(Token _ TokenIff) [iffSort] iffFirst iffSecond =
    embedParsedPattern $ IffF Iff{iffSort, iffFirst, iffSecond}
mkApply tok@(Token _ (TokenIdent _)) sorts first second =
    embedParsedPattern $ ApplicationF Application
       { applicationSymbolOrAlias = SymbolOrAlias { symbolOrAliasConstructor = mkId tok
                                                  , symbolOrAliasParams = sorts
                                                  }
       , applicationChildren = [first, second]
       }

}
