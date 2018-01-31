{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Data.Kore.Unparser.Unparse ( FromString ( fromString )
                                  , UnparseOutput
                                  , Unparse ( unparse )
                                  , unparseToString
                                  ) where

import           Control.Monad.Reader     (MonadReader, Reader, local, reader,
                                           runReader)
import           Control.Monad.Writer     (MonadWriter, WriterT, execWriterT,
                                           tell)

import           Data.Kore.AST
import           Data.Kore.Parser.CString (escapeCString)

class FromString a where
    fromString :: String -> a

class (FromString w, MonadWriter w m, MonadReader Int m)
    => UnparseOutput w m where
    write :: String -> m ()
    write s = tell (fromString s)

    betweenLines :: m ()
    betweenLines = do
        indent <- reader (`replicate` ' ')
        write "\n"
        write indent

    withIndent :: Int -> m() -> m ()
    withIndent n m = local (+n) (betweenLines >> m) >> betweenLines

class Unparse a where
    unparse :: UnparseOutput w m => a -> m ()

{-  Unparse to string instance
-}
type StringUnparser = WriterT ShowS (Reader Int)

instance FromString ShowS where
    fromString = showString

instance UnparseOutput ShowS StringUnparser where

stringUnparse :: Unparse a => a -> StringUnparser ()
stringUnparse = unparse

unparseToString :: Unparse a => a -> String
unparseToString a = showChain ""
  where
    writerAction = stringUnparse a
    readerAction = execWriterT writerAction
    showChain = runReader readerAction 0


{- unparse instances for Kore datastructures -}

instance Unparse (Id a) where
    unparse = write . getId

unparseList :: (UnparseOutput w m, Unparse a) => m () -> [a] -> m ()
unparseList _ []           = return ()
unparseList between xs = withIndent 4 (unparseList' xs)
  where
    unparseList' []      = return ()
    unparseList' [x]     = unparse x
    unparseList' (x:xs') = unparse x >> between >> unparseList' xs'

instance Unparse a => Unparse [a] where
    unparse = unparseList (write "," >> betweenLines)

withDelimiters :: UnparseOutput w m => String -> String -> m () -> m ()
withDelimiters start end m =
    write start >> m >> write end

inCurlyBraces :: UnparseOutput w m => m () -> m ()
inCurlyBraces = withDelimiters "{" "}"

inSquareBrackets :: UnparseOutput w m => m () -> m ()
inSquareBrackets = withDelimiters "[" "]"

inParens :: UnparseOutput w m => m () -> m ()
inParens = withDelimiters "(" ")"

inDoubleQuotes :: UnparseOutput w m => m () -> m ()
inDoubleQuotes = withDelimiters "\"" "\""

instance Unparse (SortVariable a) where
    unparse sv = unparse (getSortVariable sv)

instance Unparse (Sort a) where
    unparse (SortVariableSort sv) = unparse sv
    unparse (SortActualSort sa)   = do
        unparse (sortActualName sa)
        inCurlyBraces (unparse (sortActualSorts sa))

instance Unparse StringLiteral where
    unparse = inDoubleQuotes . write . escapeCString . getStringLiteral

unparseSymbolOrAliasRaw :: (UnparseOutput w m) => SymbolOrAlias a -> m ()
unparseSymbolOrAliasRaw sa = do
    unparse (symbolOrAliasConstructor sa)
    inCurlyBraces (unparse (symbolOrAliasParams sa))

unparseSymbolRaw :: (UnparseOutput w m) => Symbol a -> m ()
unparseSymbolRaw sa = do
    unparse (symbolConstructor sa)
    inCurlyBraces (unparse (symbolParams sa))

unparseAliasRaw :: (UnparseOutput w m) => Alias a -> m ()
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
    unparse AndPatternType     = write "\\and"
    unparse BottomPatternType  = write "\\bottom"
    unparse CeilPatternType    = write "\\ceil"
    unparse EqualsPatternType  = write "\\equals"
    unparse ExistsPatternType  = write "\\exists"
    unparse FloorPatternType   = write "\\floor"
    unparse ForallPatternType  = write "\\forall"
    unparse IffPatternType     = write "\\iff"
    unparse ImpliesPatternType = write "\\implies"
    unparse MemPatternType     = write "\\mem"
    unparse NotPatternType     = write "\\not"
    unparse OrPatternType      = write "\\or"
    unparse TopPatternType     = write "\\top"

unparseMLPattern
    :: (UnparseOutput w m, MLPatternClass p, Unparse rpt)
    => p a rpt -> m ()
unparseMLPattern p = do
    unparse (getPatternType p)
    inCurlyBraces (unparse (getPatternSorts p))
    inParens (unparse (getPatternPatterns p))

unparseMLBinderPattern
    :: (UnparseOutput w m, MLBinderPatternClass p, Unparse rpt,
        Unparse (UnifiedVariable v))
    => p a v rpt -> m ()
unparseMLBinderPattern p = do
    unparse (getBinderPatternType p)
    inCurlyBraces (unparse (getBinderPatternSort p))
    inParens ( do
        unparse (getBinderPatternVariable p)
        write ", "
        unparse (getBinderPatternPattern p)
        )

instance Unparse p => Unparse (And a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Application a p) where
    unparse a =
        unparse (applicationSymbolOrAlias a)
        >> inParens (unparse (applicationPatterns a))

instance Unparse (Bottom a) where
    unparse bottom = do
        unparse BottomPatternType
        inCurlyBraces (unparse (bottomSort bottom))
        inParens (return ())

instance Unparse p => Unparse (Ceil a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Equals a p) where
    unparse = unparseMLPattern

instance (Unparse (UnifiedVariable v), Unparse p)
    => Unparse (Exists a v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Floor a p) where
    unparse = unparseMLPattern

instance (Unparse (UnifiedVariable v), Unparse p)
    => Unparse (Forall a v p) where
    unparse = unparseMLBinderPattern

instance Unparse p => Unparse (Iff a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Implies a p) where
    unparse = unparseMLPattern

instance (Unparse (UnifiedVariable v), Unparse p)
    => Unparse (Mem a v p) where
    unparse m = do
        unparse MemPatternType
        inCurlyBraces (unparse [memOperandSort m, memResultSort m])
        inParens
            (unparse (memVariable m) >> write ", " >> unparse (memPattern m))

instance Unparse p => Unparse (Not a p) where
    unparse = unparseMLPattern

instance Unparse p => Unparse (Or a p) where
    unparse = unparseMLPattern

instance Unparse (Top a) where
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
    unparse (MemPattern p)           = unparse p
    unparse (NotPattern p)           = unparse p
    unparse (OrPattern p)            = unparse p
    unparse (StringLiteralPattern p) = unparse p
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
        unparse (sentenceAliasReturnSort sa)
        unparse (sentenceAliasAttributes sa)

instance Unparse (SentenceSymbol a) where
    unparse sa = do
        write "symbol"
        write " "
        unparse (sentenceSymbolSymbol sa)
        inParens (unparse (sentenceSymbolSorts sa))
        write ":"
        unparse (sentenceSymbolReturnSort sa)
        unparse (sentenceSymbolAttributes sa)

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
    unparse (SentenceAxiomSentence s)        = unparse s
    unparse (SentenceSortSentence s)         = unparse s

instance Unparse Module where
    unparse m = do
        write "module "
        unparse (moduleName m)
        withIndent 4 (
            unparseList betweenLines (moduleSentences m)
            )
        write "endmodule"
        betweenLines
        unparse (moduleAttributes m)

instance Unparse Definition where
    unparse d = do
        unparse (definitionAttributes d)
        betweenLines
        unparse (definitionModules d)
