{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-|
Module      : Data.Kore.Unparser.Unparse
Description : Class for unparsing and instances for it for 'Meta' and
              unified Kore constructs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unparser.Unparse (Unparse(..), unparseToString) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.IndentingPrinter (PrinterOutput, StringPrinter,
                                             betweenLines, printToString,
                                             withIndent, write)
import           Data.Kore.Parser.CString   (escapeCString)

import           Data.Fix

-- |'Unparse' class offers functionality to reverse the parsing process.
class Unparse a where
    unparse :: PrinterOutput w m => a -> m ()

stringUnparse :: Unparse a => a -> StringPrinter ()
stringUnparse = unparse

-- |'unparseToString' uses a 'StringPrinter' to serialize an object to 'String'.
unparseToString :: Unparse a => a -> String
unparseToString a = printToString (stringUnparse a)


{- unparse instances for Kore datastructures -}

instance Unparse (Id level) where
    unparse = write . getId

unparseList :: (PrinterOutput w m, Unparse a) => m () -> [a] -> m ()
unparseList _ []           = return ()
unparseList between xs =
    withIndent 4 (betweenLines >> unparseList' xs) >> betweenLines
  where
    unparseList' []     = return ()
    unparseList' [x]    = unparse x
    unparseList' (y:ys) = unparse y >> between >> unparseList' ys

instance Unparse a => Unparse [a] where
    unparse = unparseList (write "," >> betweenLines)

withDelimiters :: PrinterOutput w m => String -> String -> m () -> m ()
withDelimiters start end m =
    write start >> m >> write end

inCurlyBraces :: PrinterOutput w m => m () -> m ()
inCurlyBraces = withDelimiters "{" "}"

inSquareBrackets :: PrinterOutput w m => m () -> m ()
inSquareBrackets = withDelimiters "[" "]"

inParens :: PrinterOutput w m => m () -> m ()
inParens = withDelimiters "(" ")"

inDoubleQuotes :: PrinterOutput w m => m () -> m ()
inDoubleQuotes = withDelimiters "\"" "\""

inSingleQuotes :: PrinterOutput w m => m () -> m ()
inSingleQuotes = withDelimiters "\'" "\'"

instance Unparse (SortVariable level) where
    unparse sv = unparse (getSortVariable sv)

instance Unparse (Sort level) where
    unparse (SortVariableSort sv) = unparse sv
    unparse (SortActualSort sa)   = do
        unparse (sortActualName sa)
        inCurlyBraces (unparse (sortActualSorts sa))

instance Unparse StringLiteral where
    unparse = inDoubleQuotes . write . escapeCString . getStringLiteral

instance Unparse CharLiteral where
    unparse =
        inSingleQuotes . write . escapeCString . charToString . getCharLiteral
      where
        charToString c = [c]

unparseSymbolOrAliasRaw :: (PrinterOutput w m) => SymbolOrAlias level -> m ()
unparseSymbolOrAliasRaw sa = do
    unparse (symbolOrAliasConstructor sa)
    inCurlyBraces (unparse (symbolOrAliasParams sa))

unparseSymbolRaw :: (PrinterOutput w m) => Symbol level -> m ()
unparseSymbolRaw sa = do
    unparse (symbolConstructor sa)
    inCurlyBraces (unparse (symbolParams sa))

unparseAliasRaw :: (PrinterOutput w m) => Alias level -> m ()
unparseAliasRaw sa = do
    unparse (aliasConstructor sa)
    inCurlyBraces (unparse (aliasParams sa))

instance Unparse (SymbolOrAlias level) where
    unparse = unparseSymbolOrAliasRaw

instance Unparse (Alias level) where
    unparse = unparseAliasRaw

instance Unparse (Symbol level) where
    unparse = unparseSymbolRaw

instance Unparse ModuleName where
    unparse = write . getModuleName

instance Unparse (Variable level) where
    unparse var =
        unparse (variableName var) >> write ":" >> unparse (variableSort var)

instance
    ( Unparse (thing Object)
    , Unparse (thing Meta)
    ) => Unparse (Unified thing)
  where
    unparse (UnifiedObject x) = unparse x
    unparse (UnifiedMeta x)   = unparse x

instance Unparse MLPatternType where
    unparse pt = write ('\\' : patternString pt)

unparseMLPattern :: (PrinterOutput w m, MLPatternClass p, Unparse rpt)
    => p level rpt -> m ()
unparseMLPattern p = do
    unparse (getPatternType p)
    inCurlyBraces (unparse (getPatternSorts p))
    inParens (unparse (getPatternChildren p))

unparseMLBinderPattern
    :: (PrinterOutput w m, MLBinderPatternClass p, Unparse rpt,
        Unparse (v level))
    => p level v rpt -> m ()
unparseMLBinderPattern p = do
    unparse (getBinderPatternType p)
    inCurlyBraces (unparse (getBinderPatternSort p))
    inParens ( do
        unparse (getBinderPatternVariable p)
        write ", "
        unparse (getBinderPatternChild p)
        )

instance Unparse p => Unparse (And level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Application level p) where
    unparse a =
        unparse (applicationSymbolOrAlias a)
        >> inParens (unparse (applicationChildren a))

instance Unparse (Bottom level p) where
    unparse bottom = do
        unparse BottomPatternType
        inCurlyBraces (unparse (bottomSort bottom))
        inParens (return ())

instance Unparse p => Unparse (Ceil level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (DomainValue level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Equals level p) where
    unparse = unparseMLPattern

instance (Unparse (v level), Unparse p)
    => Unparse (Exists level v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Floor level p) where
    unparse = unparseMLPattern

instance (Unparse (v level), Unparse p)
    => Unparse (Forall level v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Iff level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Implies level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (In level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Next level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Not level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Or level p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Rewrites level p) where
    unparse = unparseMLPattern

instance Unparse (Top level p) where
    unparse top = do
        unparse TopPatternType
        inCurlyBraces (unparse (topSort top))
        inParens (return ())

instance (Unparse p, Unparse (v level))
    => Unparse (Pattern level v p) where
    unparse (AndPattern p)           = unparse p
    unparse (ApplicationPattern p)   = unparse p
    unparse (BottomPattern p)        = unparse p
    unparse (CeilPattern p)          = unparse p
    unparse (DomainValuePattern p)   = unparse p
    unparse (EqualsPattern p)        = unparse p
    unparse (ExistsPattern p)        = unparse p
    unparse (FloorPattern p)         = unparse p
    unparse (ForallPattern p)        = unparse p
    unparse (IffPattern p)           = unparse p
    unparse (ImpliesPattern p)       = unparse p
    unparse (InPattern p)            = unparse p
    unparse (NextPattern p)          = unparse p
    unparse (NotPattern p)           = unparse p
    unparse (OrPattern p)            = unparse p
    unparse (RewritesPattern p)      = unparse p
    unparse (StringLiteralPattern p) = unparse p
    unparse (CharLiteralPattern p)   = unparse p
    unparse (TopPattern p)           = unparse p
    unparse (VariablePattern p)      = unparse p

instance Unparse CommonKorePattern where
    unparse = applyKorePattern unparse unparse

instance Unparse (Attributes) where
    unparse = inSquareBrackets . unparse . getAttributes

instance
    (Unparse (Fix (pat variable)), Unparse (variable level)) => Unparse (SentenceAlias level pat variable)
  where
    unparse sa = do
        write "alias"
        write " "
        unparse (sentenceAliasAlias sa)
        inParens (unparse (sentenceAliasSorts sa))
        write " "
        write ":"
        write " "
        unparse (sentenceAliasResultSort sa)
        write "\n"
        write "where"
        write " "
        unparse (sentenceAliasLeftPattern sa)
        write " "
        write ":="
        write " "
        unparse (sentenceAliasRightPattern sa)
        unparse (sentenceAliasAttributes sa)

instance
    Unparse (Fix (pat variable)) => Unparse (SentenceSymbol level pat variable)
  where
    unparse sa = do
        write "symbol"
        write " "
        unparse (sentenceSymbolSymbol sa)
        inParens (unparse (sentenceSymbolSorts sa))
        write ":"
        unparse (sentenceSymbolResultSort sa)
        unparse (sentenceSymbolAttributes sa)

instance
    Unparse (Fix (pat variable)) => Unparse (SentenceImport pat variable)
  where
    unparse a = do
        write "import"
        write " "
        unparse (sentenceImportModuleName a)
        unparse (sentenceImportAttributes a)

instance
    ( Unparse param
    , Unparse (Fix (pat variable))
    ) => Unparse (SentenceAxiom param pat variable)
  where
    unparse a = do
        write "axiom"
        inCurlyBraces (unparse (sentenceAxiomParameters a))
        unparse (sentenceAxiomPattern a)
        unparse (sentenceAxiomAttributes a)

instance
    Unparse (Fix (pat variable)) => Unparse (SentenceSort level pat variable)
  where
    unparse a = do
        write "sort"
        write " "
        unparse (sentenceSortName a)
        inCurlyBraces (unparse (sentenceSortParameters a))
        unparse (sentenceSortAttributes a)

instance
    Unparse (Fix (pat variable)) => Unparse (SentenceHook level pat variable)
  where
    unparse (SentenceHookedSort a) = do
        write "hooked-"
        unparse a
    unparse (SentenceHookedSymbol a) = do
        write "hooked-"
        unparse a

instance
    ( Unparse sortParam
    , Unparse (Fix (pat variable))
    , Unparse (variable level)
    ) => Unparse (Sentence level sortParam pat variable)
  where
    unparse (SentenceAliasSentence s)  = unparse s
    unparse (SentenceSymbolSentence s) = unparse s
    unparse (SentenceImportSentence s) = unparse s
    unparse (SentenceAxiomSentence s)  = unparse s
    unparse (SentenceSortSentence s)   = unparse s
    unparse (SentenceHookSentence s)   = unparse s

instance
    ( Unparse sortParam
    , Unparse (Fix (pat variable))
    , Unparse (variable Meta)
    , Unparse (variable Object)
    ) => Unparse (UnifiedSentence sortParam pat variable)
  where
    unparse = applyUnifiedSentence unparse unparse

instance
    ( Unparse (sentence sortParam pat variable)
    , Unparse (Fix (pat variable))
    ) => Unparse (Module sentence sortParam pat variable)
  where
    unparse m = do
        write "module "
        unparse name
        if null sentences
            then betweenLines
            else do
                withIndent 4
                    (  betweenLines
                    >> unparseList betweenLines sentences
                    )
                betweenLines
        write "endmodule"
        betweenLines
        unparse attributes
      where
        name =moduleName m
        sentences = moduleSentences m
        attributes = moduleAttributes m

instance
    ( Unparse (sentence sortParam pat variable)
    , Unparse (Fix (pat variable))
    ) => Unparse (Definition sentence sortParam pat variable)
  where
    unparse d = do
        unparse (definitionAttributes d)
        betweenLines
        unparseList betweenLines (definitionModules d)

instance Unparse (Fix (Pattern Meta Variable)) where
    unparse = unparse . unFix
