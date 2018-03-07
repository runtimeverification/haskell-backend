{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Unparser.Unparse (Unparse, unparseToString) where

import           Data.Kore.AST
import           Data.Kore.IndentingPrinter (PrinterOutput, StringPrinter,
                                             betweenLines, printToString,
                                             withIndent, write)
import           Data.Kore.Parser.CString   (escapeCString)

{-  Unparse to string instance
-}
class Unparse a where
    unparse :: PrinterOutput w m => a -> m ()

stringUnparse :: Unparse a => a -> StringPrinter ()
stringUnparse = unparse

unparseToString :: Unparse a => a -> String
unparseToString a = printToString (stringUnparse a)


{- unparse instances for Kore datastructures -}

instance Unparse (Id a) where
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

instance Unparse (SortVariable a) where
    unparse sv = unparse (getSortVariable sv)

instance Unparse (Sort a) where
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

unparseSymbolOrAliasRaw :: (PrinterOutput w m) => SymbolOrAlias a -> m ()
unparseSymbolOrAliasRaw sa = do
    unparse (symbolOrAliasConstructor sa)
    inCurlyBraces (unparse (symbolOrAliasParams sa))

unparseSymbolRaw :: (PrinterOutput w m) => Symbol a -> m ()
unparseSymbolRaw sa = do
    unparse (symbolConstructor sa)
    inCurlyBraces (unparse (symbolParams sa))

unparseAliasRaw :: (PrinterOutput w m) => Alias a -> m ()
unparseAliasRaw sa = do
    unparse (aliasConstructor sa)
    inCurlyBraces (unparse (aliasParams sa))

instance Unparse (SymbolOrAlias a) where
    unparse = unparseSymbolOrAliasRaw

instance Unparse (Alias a) where
    unparse = unparseAliasRaw

instance Unparse (Symbol a) where
    unparse = unparseSymbolRaw

instance Unparse ModuleName where
    unparse = write . getModuleName

instance Unparse (Variable a) where
    unparse var =
        unparse (variableName var) >> write ":" >> unparse (variableSort var)

instance Unparse UnifiedSortVariable where
    unparse (ObjectSortVariable sv) = unparse sv
    unparse (MetaSortVariable sv)   = unparse sv

instance Unparse (UnifiedVariable Variable) where
    unparse (ObjectVariable sv) = unparse sv
    unparse (MetaVariable sv)   = unparse sv

instance Unparse UnifiedPattern where
    unparse (ObjectPattern sv) = unparse sv
    unparse (MetaPattern sv)   = unparse sv


instance Unparse MLPatternType where
    unparse pt = write ('\\' : patternString pt)

unparseMLPattern :: (PrinterOutput w m, MLPatternClass p, Unparse rpt)
    => p a rpt -> m ()
unparseMLPattern p = do
    unparse (getPatternType p)
    inCurlyBraces (unparse (getPatternSorts p))
    inParens (unparse (getPatternChildren p))

unparseMLBinderPattern
    :: (PrinterOutput w m, MLBinderPatternClass p, Unparse rpt,
        Unparse (v a))
    => p a v rpt -> m ()
unparseMLBinderPattern p = do
    unparse (getBinderPatternType p)
    inCurlyBraces (unparse (getBinderPatternSort p))
    inParens ( do
        unparse (getBinderPatternVariable p)
        write ", "
        unparse (getBinderPatternChild p)
        )

instance Unparse p => Unparse (And a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Application a p) where
    unparse a =
        unparse (applicationSymbolOrAlias a)
        >> inParens (unparse (applicationChildren a))

instance Unparse (Bottom a p) where
    unparse bottom = do
        unparse BottomPatternType
        inCurlyBraces (unparse (bottomSort bottom))
        inParens (return ())

instance Unparse p => Unparse (Ceil a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Equals a p) where
    unparse = unparseMLPattern

instance (Unparse (v a), Unparse p)
    => Unparse (Exists a v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Floor a p) where
    unparse = unparseMLPattern

instance (Unparse (v a), Unparse p)
    => Unparse (Forall a v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Iff a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Implies a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (In a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Next a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Not a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Or a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Rewrites a p) where
    unparse = unparseMLPattern

instance Unparse (Top a p) where
    unparse top = do
        unparse TopPatternType
        inCurlyBraces (unparse (topSort top))
        inParens (return ())

instance (Unparse (UnifiedVariable v), Unparse p, Unparse (v a))
    => Unparse (Pattern a v p) where
    unparse (AndPattern p)           = unparse p
    unparse (ApplicationPattern p)   = unparse p
    unparse (BottomPattern p)        = unparse p
    unparse (CeilPattern p)          = unparse p
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

instance Unparse Attributes where
    unparse = inSquareBrackets . unparse . getAttributes

instance Unparse (SentenceAlias a) where
    unparse sa = do
        write "alias"
        write " "
        unparse (sentenceAliasAlias sa)
        inParens (unparse (sentenceAliasSorts sa))
        write ":"
        unparse (sentenceAliasResultSort sa)
        unparse (sentenceAliasAttributes sa)

instance Unparse (SentenceSymbol a) where
    unparse sa = do
        write "symbol"
        write " "
        unparse (sentenceSymbolSymbol sa)
        inParens (unparse (sentenceSymbolSorts sa))
        write ":"
        unparse (sentenceSymbolResultSort sa)
        unparse (sentenceSymbolAttributes sa)

instance Unparse SentenceImport where
    unparse a = do
        write "import"
        write " "
        unparse (sentenceImportModuleName a)
        unparse (sentenceImportAttributes a)

instance Unparse SentenceAxiom where
    unparse a = do
        write "axiom"
        inCurlyBraces (unparse (sentenceAxiomParameters a))
        unparse (sentenceAxiomPattern a)
        unparse (sentenceAxiomAttributes a)

instance Unparse SentenceSort where
    unparse a = do
        write "sort"
        write " "
        unparse (sentenceSortName a)
        inCurlyBraces (unparse (sentenceSortParameters a))
        unparse (sentenceSortAttributes a)

instance Unparse Sentence where
    unparse (MetaSentenceAliasSentence s)    = unparse s
    unparse (ObjectSentenceAliasSentence s)  = unparse s
    unparse (MetaSentenceSymbolSentence s)   = unparse s
    unparse (ObjectSentenceSymbolSentence s) = unparse s
    unparse (SentenceImportSentence s)       = unparse s
    unparse (SentenceAxiomSentence s)        = unparse s
    unparse (SentenceSortSentence s)         = unparse s

instance Unparse Module where
    unparse m = do
        write "module "
        unparse (moduleName m)
        if moduleSentences m /= []
            then do
                withIndent 4
                    (  betweenLines
                    >> unparseList betweenLines (moduleSentences m)
                    )
                betweenLines
            else betweenLines
        write "endmodule"
        betweenLines
        unparse (moduleAttributes m)

instance Unparse Definition where
    unparse d = do
        unparse (definitionAttributes d)
        betweenLines
        unparseList betweenLines (definitionModules d)
