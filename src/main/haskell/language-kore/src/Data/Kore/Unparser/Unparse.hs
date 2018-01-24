{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Unparser.Unparse where

import           Control.Monad.Reader
import           Control.Monad.Writer
import           Data.Foldable            (sequence_)

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
        indent <- reader (flip replicate ' ')
        write "\n"
        write indent

    withIndent :: Int -> m() -> m ()
    withIndent n m = local (+n) (betweenLines >> m)

class Unparse a where
    unparse :: UnparseOutput w m => a -> m ()

instance Unparse (Id a) where
    unparse = write . getId

intersperseM_ :: Monad m => m () -> [m ()] -> m ()
intersperseM_ _ []       = return ()
intersperseM_ _ [x]      = x
intersperseM_ btw (x:xs) = x >> btw >> intersperseM_ btw xs

instance Unparse a => Unparse [a] where
    unparse []     = return ()
    unparse [x]    = unparse x
    unparse (x:xs) = unparse x >> write ", " >> unparse xs

inCurlyBraces :: UnparseOutput w m => m () -> m ()
inCurlyBraces m = write "{" >> withIndent 4 m >> write "}"

inSquareBrackets :: UnparseOutput w m => m () -> m ()
inSquareBrackets m = write "{" >> withIndent 4 m >> write "}"

inParens :: UnparseOutput w m => m () -> m ()
inParens m = write "{" >> withIndent 4 m >> write "}"

instance Unparse (SortVariable a) where
    unparse sv = unparse (getSortVariable sv)

instance Unparse (Sort a) where
    unparse (SortVariableSort sv) = unparse sv
    unparse (SortActualSort sa)   = do
        unparse (sortActualName sa)
        inCurlyBraces (unparse (sortActualSorts sa))

instance Unparse StringLiteral where
    unparse = write . escapeCString . getStringLiteral

unparseSymbolOrAliasRaw
    :: (UnparseOutput w m, SymbolOrAliasClass s)
    => s a -> m ()
unparseSymbolOrAliasRaw sa = do
    unparse (getSymbolOrAliasConstructor sa)
    inCurlyBraces (unparse (getSymbolOrAliasParams sa))

instance Unparse (SymbolOrAlias a) where
    unparse = unparseSymbolOrAliasRaw

instance Unparse (Alias a) where
    unparse = unparseSymbolOrAliasRaw

instance Unparse (Symbol a) where
    unparse = unparseSymbolOrAliasRaw

instance Unparse ModuleName where
    unparse = write . getModuleName

instance Unparse (Variable a) where
    unparse var =
        unparse (variableName var) >> write ":" >> unparse (variableSort var)

instance Unparse UnifiedSortVariable where
    unparse (ObjectSortVariable sv) = unparse sv
    unparse (MetaSortVariable sv)   = unparse sv

instance Unparse UnifiedVariable where
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

unparseMLPattern :: (UnparseOutput w m, MLPatternClass p) => p a -> m ()
unparseMLPattern p = do
    unparse (getPatternType p)
    inCurlyBraces (unparse (getPatternSorts p))
    inParens (unparse (getPatternPatterns p))

unparseMLBinderPattern
    :: (UnparseOutput w m, MLBinderPatternClass p) => p a -> m ()
unparseMLBinderPattern p = do
    unparse (getBinderPatternType p)
    inCurlyBraces (unparse (getBinderPatternSort p))
    inParens ( do
        unparse (getBinderPatternVariable p)
        write ", "
        unparse (getBinderPatternPattern p)
        )

instance Unparse (And a) where
    unparse = unparseMLPattern

instance Unparse (Application a) where
    unparse a =
        unparse (applicationSymbolOrAlias a)
        >> inParens (unparse (applicationPatterns a))

instance Unparse (Bottom a) where
    unparse = unparseMLPattern

instance Unparse (Ceil a) where
    unparse = unparseMLPattern

instance Unparse (Equals a) where
    unparse = unparseMLPattern

instance Unparse (Exists a) where
    unparse = unparseMLBinderPattern

instance Unparse (Floor a) where
    unparse = unparseMLPattern

instance Unparse (Forall a) where
    unparse = unparseMLBinderPattern

instance Unparse (Iff a) where
    unparse = unparseMLPattern

instance Unparse (Implies a) where
    unparse = unparseMLPattern

instance Unparse (Mem a) where
    unparse m = do
        unparse MemPatternType
        inCurlyBraces (unparse [memOperandSort m, memResultSort m])
        inParens
            (unparse (memVariable m) >> write ", " >> unparse (memPattern m))

instance Unparse (Not a) where
    unparse = unparseMLPattern

instance Unparse (Or a) where
    unparse = unparseMLPattern

instance Unparse (Top a) where
    unparse = unparseMLPattern

instance Unparse (Pattern a) where
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

instance Unparse (SentenceSymbol a) where
    unparse sa = do
        write "alias"
        write " "
        unparse (sentenceSymbolSymbol sa)
        inParens (unparse (sentenceSymbolSorts sa))
        write ":"
        unparse (sentenceSymbolReturnSort sa)

instance Unparse SentenceAxiom where
    unparse a = do
        write "axiom"
        inCurlyBraces (unparse (sentenceAxiomParameters a))
        unparse (sentenceAxiomPattern a)
        unparse (sentenceAxiomAtrributes a)

instance Unparse SentenceSort where
    unparse a = do
        write "sort"
        inCurlyBraces (unparse (sentenceSortParameters a))
        unparse (sentenceSortSort a)
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
        betweenLines
        withIndent 4 (
            intersperseM_ betweenLines (map unparse (moduleSentences m))
            )
        betweenLines
        write "endmodule"
        betweenLines
        unparse (moduleAttributes m)

instance Unparse Definition where
    unparse d = do
        unparse (definitionAttributes d)
        unparse (definitionModules d)
