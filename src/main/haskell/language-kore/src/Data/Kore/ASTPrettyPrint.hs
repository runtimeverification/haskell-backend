{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Data.Kore.ASTPrettyPrint (prettyPrintToString) where

import           Control.Monad.Reader
import           Control.Monad.Writer

import           Data.Kore.AST
import           Data.Kore.Parser.CString (escapeCString)
import           Data.List (intersperse)

{-# ANN module "HLint: ignore Use record patterns" #-}
{-
This module uses the following pattern repeatedly:
instance PrettyPrint Something where
    prettyPrint s@(Something _ _ _ ...) =
        writeStructure "Something"
            [ writeField "something1" something1 s
            , writeField "something2" something2 s
            ....
            ]

This pattern does a few things, which are very nice to have in a pretty printer:
1. Makes sure that we will notice when the number of fields in Something
   changes (done by matching on (Something _ _ _ ...)).
2. Makes sure that the code still works when the field order changes
   (done by using the something<n> accessors).
3. Makes sure that we notice when field names change (again, done by using
   the something<n> accessors).

However, this generates the HLint error disabled above.
-}

class FromString a where
    fromString :: String -> a

class (FromString w, MonadWriter w m, MonadReader Int m)
    => PrettyPrintOutput w m where
    write :: String -> m ()
    write s = tell (fromString s)

    betweenLines :: m ()
    betweenLines = do
        indent <- reader (`replicate` ' ')
        write "\n"
        write indent

    withIndent :: Int -> m () -> m ()
    withIndent n = local (+n)

data Flags = NeedsParentheses | MaySkipParentheses

class PrettyPrint a where
    prettyPrint :: PrettyPrintOutput w m => Flags -> a -> m ()

{-  Unparse to string instance
-}
type StringPrettyPrinter = WriterT ShowS (Reader Int)

instance FromString ShowS where
    fromString = showString

instance PrettyPrintOutput ShowS StringPrettyPrinter where

stringPrettyPrint :: PrettyPrint a => Flags -> a -> StringPrettyPrinter ()
stringPrettyPrint = prettyPrint

prettyPrintToString :: PrettyPrint a => a -> String
prettyPrintToString a = showChain ""
  where
    writerAction = stringPrettyPrint MaySkipParentheses a
    readerAction = execWriterT writerAction
    showChain = runReader readerAction 0

{- utility functions -}

betweenParentheses :: PrettyPrintOutput w m => Flags -> m() -> m()
betweenParentheses NeedsParentheses thing = do
    write "("
    thing
    write ")"
betweenParentheses MaySkipParentheses thing = thing

writeOneFieldStruct
    :: (PrettyPrintOutput w m, PrettyPrint a)
    => Flags -> String -> a -> m ()
writeOneFieldStruct flags name content =
    betweenParentheses
        flags
        (do
            write name
            write " "
            prettyPrint NeedsParentheses content
        )

writeOneFieldStructNewLine
    :: (PrettyPrintOutput w m, PrettyPrint a)
    => Flags -> String -> a -> m ()
writeOneFieldStructNewLine flags name content =
    betweenParentheses
        flags
        (do
            write name
            withIndent 4 (prettyPrint NeedsParentheses content)
        )

writeFieldOneLine
    :: (PrettyPrintOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeFieldOneLine fieldName field object = do
    write fieldName
    write " = "
    prettyPrint MaySkipParentheses (field object)

writeListField
    :: (PrettyPrintOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeListField fieldName field object = do
    write fieldName
    write " ="
    prettyPrint MaySkipParentheses (field object)

writeFieldNewLine
    :: (PrettyPrintOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeFieldNewLine fieldName field object = do
    write fieldName
    write " ="
    withIndent 4
        (betweenLines >> prettyPrint MaySkipParentheses (field object))

writeAttributesField
    :: (PrettyPrintOutput w m)
    => String
    -> Attributes
    -> m ()
writeAttributesField fieldName (Attributes []) = do
    write fieldName
    write " = Attributes []"
writeAttributesField fieldName attributes = do
    write fieldName
    write " ="
    withIndent 4
        (betweenLines >> prettyPrint MaySkipParentheses attributes)

writeStructure :: PrettyPrintOutput w m => String -> [m ()] -> m ()
writeStructure name fields =
    write name >> inCurlyBracesIndent (printableList fields)

printableList :: PrettyPrintOutput w m => [m ()] -> [m ()]
printableList = intersperse (betweenLines >> write ", ")

instance (IsMeta a) => PrettyPrint (Id a) where
    prettyPrint flags id'@(Id name) =
        betweenParentheses
            flags
            (do
                write "Id "
                write (if isObject id' then "Object" else "Meta")
                write " \""
                write name
                write "\""
            )

instance PrettyPrint a => PrettyPrint [a] where
    prettyPrint _ list =
        inSquareBracketsIndent
            (printableList (map (prettyPrint MaySkipParentheses) list))

listWithDelimiters
    :: PrettyPrintOutput w m => String -> String -> [m ()] -> m ()
listWithDelimiters start end [] =
    write " " >> write start >> write end
listWithDelimiters start end list =
    withIndent 4 (do
        betweenLines
        write start
        write " "
        sequence_ list
        betweenLines >> write end)

inCurlyBracesIndent :: PrettyPrintOutput w m => [m ()] -> m ()
inCurlyBracesIndent = listWithDelimiters "{" "}"

inSquareBracketsIndent :: PrettyPrintOutput w m => [m ()] -> m ()
inSquareBracketsIndent = listWithDelimiters "[" "]"

inDoubleQuotes :: PrettyPrintOutput w m => m () -> m ()
inDoubleQuotes thing = write "\"" >> thing >> write "\""

instance (IsMeta a) => PrettyPrint (SortVariable a) where
    prettyPrint flags sv =
        writeOneFieldStruct flags "SortVariable" (getSortVariable sv)

instance (IsMeta a) => PrettyPrint (Sort a) where
    prettyPrint flags (SortVariableSort sv) =
        writeOneFieldStruct flags "SortVariableSort" sv
    prettyPrint flags (SortActualSort sa)   =
        writeOneFieldStructNewLine flags "SortActualSort" sa

instance (IsMeta a) => PrettyPrint (SortActual a) where
    prettyPrint _ sa@(SortActual _ _) =
        writeStructure "SortActual"
            [ writeFieldOneLine "sortActualName" sortActualName sa
            , writeListField "sortActualSorts" sortActualSorts sa
            ]

instance PrettyPrint StringLiteral where
    prettyPrint flags s@(StringLiteral _) =
        betweenParentheses
            flags
            (  write "StringLiteral "
            >> inDoubleQuotes (write (escapeCString (getStringLiteral s)))
            )

instance (IsMeta a) => PrettyPrint (SymbolOrAlias a) where
    prettyPrint _ s@(SymbolOrAlias _ _) =
        writeStructure "SymbolOrAlias"
            [ writeFieldOneLine
                "symbolOrAliasConstructor" symbolOrAliasConstructor s
            , writeListField "symbolOrAliasParams" symbolOrAliasParams s
            ]

instance (IsMeta a) => PrettyPrint (Alias a) where
    prettyPrint _ s@(Alias _ _) =
        writeStructure "Alias"
            [ writeFieldOneLine "aliasConstructor" aliasConstructor s
            , writeListField "aliasParams" aliasParams s
            ]

instance (IsMeta a) => PrettyPrint (Symbol a) where
    prettyPrint _ s@(Symbol _ _) =
        writeStructure "Symbol"
            [ writeFieldOneLine "symbolConstructor" symbolConstructor s
            , writeListField "symbolParams" symbolParams s
            ]

instance PrettyPrint ModuleName where
    prettyPrint flags s@(ModuleName _) =
        betweenParentheses
            flags
            ( write "ModuleName "
            >> inDoubleQuotes (write (getModuleName s))
            )

instance (IsMeta a) => PrettyPrint (Variable a) where
    prettyPrint _ var@(Variable _ _) =
        writeStructure "Variable"
            [ writeFieldOneLine "variableName" variableName var
            , writeFieldNewLine "variableSort" variableSort var
            ]

instance PrettyPrint UnifiedSortVariable where
    prettyPrint flags (ObjectSortVariable sv) =
        writeOneFieldStruct flags "ObjectSortVariable" sv
    prettyPrint flags (MetaSortVariable sv)   =
        writeOneFieldStruct flags "MetaSortVariable" sv

instance PrettyPrint UnifiedVariable where
    prettyPrint flags (ObjectVariable sv) =
        writeOneFieldStruct flags "ObjectVariable" sv
    prettyPrint flags (MetaVariable sv)   =
        writeOneFieldStruct flags "SortVariable" sv

instance PrettyPrint UnifiedPattern where
    prettyPrint flags (ObjectPattern sv) =
        writeOneFieldStruct flags "ObjectPattern" sv
    prettyPrint flags (MetaPattern sv)   =
        writeOneFieldStruct flags "MetaPattern" sv

instance (IsMeta a) => PrettyPrint (And a) where
    prettyPrint _ p@(And _ _ _) =
        writeStructure
            "And"
            [ writeFieldNewLine "andSort" andSort p
            , writeFieldNewLine "andFirst" andFirst p
            , writeFieldNewLine "andSecond" andSecond p
            ]

instance (IsMeta a) => PrettyPrint (Application a) where
    prettyPrint _ p@(Application _ _) =
        writeStructure
            "Application"
            [ writeFieldNewLine
                "applicationSymbolOrAlias" applicationSymbolOrAlias p
            , writeListField "applicationPatterns" applicationPatterns p
            ]

instance (IsMeta a) => PrettyPrint (Bottom a) where
    prettyPrint flags (Bottom p) =
        writeOneFieldStruct flags "Bottom" p

instance (IsMeta a) => PrettyPrint (Ceil a) where
    prettyPrint _ p@(Ceil _ _ _) =
        writeStructure
            "Ceil"
            [ writeFieldNewLine "ceilOperandSort" ceilOperandSort p
            , writeFieldNewLine "ceilResultSort" ceilResultSort p
            , writeFieldNewLine "ceilPattern" ceilPattern p
            ]

instance (IsMeta a) => PrettyPrint (Equals a) where
    prettyPrint _ p@(Equals _ _ _ _) =
        writeStructure
            "Equals"
            [ writeFieldNewLine "equalsOperandSort" equalsOperandSort p
            , writeFieldNewLine "equalsResultSort" equalsResultSort p
            , writeFieldNewLine "equalsFirst" equalsFirst p
            , writeFieldNewLine "equalsSecond" equalsSecond p
            ]

instance (IsMeta a) => PrettyPrint (Exists a) where
    prettyPrint _ p@(Exists _ _ _) =
        writeStructure
            "Exists"
            [ writeFieldNewLine "existsSort" existsSort p
            , writeFieldNewLine "existsVariable" existsVariable p
            , writeFieldNewLine "existsPattern" existsPattern p
            ]

instance (IsMeta a) => PrettyPrint (Floor a) where
    prettyPrint _ p@(Floor _ _ _) =
        writeStructure
            "Floor"
            [ writeFieldNewLine "floorOperandSort" floorOperandSort p
            , writeFieldNewLine "floorResultSort" floorResultSort p
            , writeFieldNewLine "floorPattern" floorPattern p
            ]

instance (IsMeta a) => PrettyPrint (Forall a) where
    prettyPrint _ p@(Forall _ _ _) =
        writeStructure
            "Forall"
            [ writeFieldNewLine "forallSort" forallSort p
            , writeFieldNewLine "forallVariable" forallVariable p
            , writeFieldNewLine "forallPattern" forallPattern p
            ]

instance (IsMeta a) => PrettyPrint (Iff a) where
    prettyPrint _ p@(Iff _ _ _) =
        writeStructure
            "Iff"
            [ writeFieldNewLine "iffSort" iffSort p
            , writeFieldNewLine "iffFirst" iffFirst p
            , writeFieldNewLine "iffSecond" iffSecond p
            ]

instance (IsMeta a) => PrettyPrint (Implies a) where
    prettyPrint _ p@(Implies _ _ _) =
        writeStructure
            "Implies"
            [ writeFieldNewLine "impliesSort" impliesSort p
            , writeFieldNewLine "impliesFirst" impliesFirst p
            , writeFieldNewLine "impliesSecond" impliesSecond p
            ]

instance (IsMeta a) => PrettyPrint (Mem a) where
    prettyPrint _ p@(Mem _ _ _ _) =
        writeStructure
            "Mem"
            [ writeFieldNewLine "memOperandSort" memOperandSort p
            , writeFieldNewLine "memResultSort" memResultSort p
            , writeFieldNewLine "memVariable" memVariable p
            , writeFieldNewLine "memPattern" memPattern p
            ]

instance (IsMeta a) => PrettyPrint (Not a) where
    prettyPrint _ p@(Not _ _) =
        writeStructure
            "Not"
            [ writeFieldNewLine "notSort" notSort p
            , writeFieldNewLine "notPattern" notPattern p
            ]

instance (IsMeta a) => PrettyPrint (Or a) where
    prettyPrint _ p@(Or _ _ _) =
        writeStructure
            "Or"
            [ writeFieldNewLine "orSort" orSort p
            , writeFieldNewLine "orFirst" orFirst p
            , writeFieldNewLine "orSecond" orSecond p
            ]

instance (IsMeta a) => PrettyPrint (Top a) where
    prettyPrint flags (Top p) =
        writeOneFieldStruct flags "Top" p

instance (IsMeta a) => PrettyPrint (Pattern a) where
    prettyPrint flags (AndPattern p) =
        writeOneFieldStruct flags "AndPattern" p
    prettyPrint flags (ApplicationPattern p) =
        writeOneFieldStruct flags "ApplicationPattern" p
    prettyPrint flags (BottomPattern p) =
        writeOneFieldStruct flags "BottomPattern" p
    prettyPrint flags (CeilPattern p) =
        writeOneFieldStruct flags "CeilPattern" p
    prettyPrint flags (EqualsPattern p) =
        writeOneFieldStruct flags "EqualsPattern" p
    prettyPrint flags (ExistsPattern p) =
        writeOneFieldStruct flags "ExistsPattern" p
    prettyPrint flags (FloorPattern p) =
        writeOneFieldStruct flags "FloorPattern" p
    prettyPrint flags (ForallPattern p) =
        writeOneFieldStruct flags "ForallPattern" p
    prettyPrint flags (IffPattern p) =
        writeOneFieldStruct flags "IffPattern" p
    prettyPrint flags (ImpliesPattern p)       =
        writeOneFieldStruct flags "ImpliesPattern" p
    prettyPrint flags (MemPattern p) =
        writeOneFieldStruct flags "MemPattern" p
    prettyPrint flags (NotPattern p) =
        writeOneFieldStruct flags "NotPattern" p
    prettyPrint flags (OrPattern p) =
        writeOneFieldStruct flags "OrPattern" p
    prettyPrint flags (StringLiteralPattern p) =
        writeOneFieldStruct flags "StringLiteralPattern" p
    prettyPrint flags (TopPattern p) =
        writeOneFieldStruct flags "TopPattern" p
    prettyPrint flags (VariablePattern p) =
        writeOneFieldStruct flags "VariablePattern" p

instance PrettyPrint Attributes where
    prettyPrint flags (Attributes a) = writeOneFieldStruct flags "Attributes" a

instance (IsMeta a) => PrettyPrint (SentenceAlias a) where
    prettyPrint _ sa@(SentenceAlias _ _ _ _) =
        writeStructure
            "SentenceAlias"
            [ writeFieldNewLine "sentenceAliasAlias" sentenceAliasAlias sa
            , writeListField "sentenceAliasSorts" sentenceAliasSorts sa
            , writeFieldNewLine
                "sentenceAliasReturnSort" sentenceAliasReturnSort sa
            , writeAttributesField
                "sentenceAliasAttributes" (sentenceAliasAttributes sa)
            ]

instance (IsMeta a) => PrettyPrint (SentenceSymbol a) where
    prettyPrint _ sa@(SentenceSymbol _ _ _ _) =
        writeStructure
            "SentenceSymbol"
            [ writeFieldNewLine "sentenceSymbolSymbol" sentenceSymbolSymbol sa
            , writeListField "sentenceSymbolSorts" sentenceSymbolSorts sa
            , writeFieldNewLine
                "sentenceSymbolReturnSort" sentenceSymbolReturnSort sa
            , writeAttributesField
                "sentenceSymbolAttributes" (sentenceSymbolAttributes sa)
            ]

instance PrettyPrint SentenceAxiom where
    prettyPrint _ sa@(SentenceAxiom _ _ _) =
        writeStructure
            "SentenceAxiom"
            [ writeListField
                "sentenceAxiomParameters" sentenceAxiomParameters sa
            , writeFieldNewLine
                "sentenceAxiomPattern" sentenceAxiomPattern sa
            , writeAttributesField
                "sentenceAxiomAttributes" (sentenceAxiomAttributes sa)
            ]

instance PrettyPrint SentenceSort where
    prettyPrint _ sa@(SentenceSort _ _ _) =
        writeStructure
            "SentenceSort"
            [ writeFieldOneLine "sentenceSortName" sentenceSortName sa
            , writeListField
                "sentenceSortParameters" sentenceSortParameters sa
            , writeAttributesField
                "sentenceSortAttributes" (sentenceSortAttributes sa)
            ]

instance PrettyPrint Sentence where
    prettyPrint flags (MetaSentenceAliasSentence s)    =
        writeOneFieldStruct flags "MetaSentenceAliasSentence" s
    prettyPrint flags (ObjectSentenceAliasSentence s)  =
        writeOneFieldStruct flags "ObjectSentenceAliasSentence" s
    prettyPrint flags (MetaSentenceSymbolSentence s)   =
        writeOneFieldStruct flags "MetaSentenceSymbolSentence" s
    prettyPrint flags (ObjectSentenceSymbolSentence s) =
        writeOneFieldStruct flags "ObjectSentenceSymbolSentence" s
    prettyPrint flags (SentenceAxiomSentence s)        =
        writeOneFieldStruct flags "SentenceAxiomSentence" s
    prettyPrint flags (SentenceSortSentence s)         =
        writeOneFieldStruct flags "SentenceSortSentence" s

instance PrettyPrint Module where
    prettyPrint _ m@(Module _ _ _) =
        writeStructure
            "Module"
            [ writeFieldOneLine "moduleName" moduleName m
            , writeListField "moduleSentences" moduleSentences m
            , writeAttributesField "moduleAttributes" (moduleAttributes m)
            ]

instance PrettyPrint Definition where
    prettyPrint _ d@(Definition _ _) =
        writeStructure
            "Definition"
            [ writeAttributesField
                "definitionAttributes" (definitionAttributes d)
            , writeFieldNewLine "definitionModules" definitionModules d
            ]
