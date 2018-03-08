{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.ASTPrettyPrint (prettyPrintToString) where

import           Data.Kore.AST
import           Data.Kore.IndentingPrinter (PrinterOutput, StringPrinter,
                                             betweenLines, printToString,
                                             withIndent, write)
import           Data.Kore.Parser.CString   (escapeCString)
import           Data.List                  (intersperse)

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

data Flags = NeedsParentheses | MaySkipParentheses

{-  Print to string instance
-}

class PrettyPrint a where
    prettyPrint :: PrinterOutput w m => Flags -> a -> m ()

stringPrettyPrint :: PrettyPrint a => Flags -> a -> StringPrinter ()
stringPrettyPrint = prettyPrint

prettyPrintToString :: PrettyPrint a => a -> String
prettyPrintToString a = printToString (stringPrettyPrint MaySkipParentheses a)

{- utility functions -}

betweenParentheses :: PrinterOutput w m => Flags -> m() -> m()
betweenParentheses NeedsParentheses thing = do
    write "("
    thing
    write ")"
betweenParentheses MaySkipParentheses thing = thing

writeOneFieldStruct
    :: (PrinterOutput w m, PrettyPrint a)
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
    :: (PrinterOutput w m, PrettyPrint a)
    => Flags -> String -> a -> m ()
writeOneFieldStructNewLine flags name content =
    betweenParentheses
        flags
        (do
            write name
            withIndent 4 (prettyPrint NeedsParentheses content)
        )

writeFieldOneLine
    :: (PrinterOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeFieldOneLine fieldName field object = do
    write fieldName
    write " = "
    prettyPrint MaySkipParentheses (field object)

writeListField
    :: (PrinterOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeListField fieldName field object = do
    write fieldName
    write " ="
    prettyPrint MaySkipParentheses (field object)

writeFieldNewLine
    :: (PrinterOutput w m, PrettyPrint a) => String -> (b -> a) -> b -> m ()
writeFieldNewLine fieldName field object = do
    write fieldName
    write " ="
    withIndent 4
        (betweenLines >> prettyPrint MaySkipParentheses (field object))

writeAttributesField
    :: (PrinterOutput w m)
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

writeStructure :: PrinterOutput w m => String -> [m ()] -> m ()
writeStructure name fields =
    write name >> inCurlyBracesIndent (printableList fields)

printableList :: PrinterOutput w m => [m ()] -> [m ()]
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
    :: PrinterOutput w m => String -> String -> [m ()] -> m ()
listWithDelimiters start end [] =
    write " " >> write start >> write end
listWithDelimiters start end list =
    withIndent 4 (do
        betweenLines
        write start
        write " "
        sequence_ list
        betweenLines >> write end)

inCurlyBracesIndent :: PrinterOutput w m => [m ()] -> m ()
inCurlyBracesIndent = listWithDelimiters "{" "}"

inSquareBracketsIndent :: PrinterOutput w m => [m ()] -> m ()
inSquareBracketsIndent = listWithDelimiters "[" "]"

inDoubleQuotes :: PrinterOutput w m => m () -> m ()
inDoubleQuotes thing = write "\"" >> thing >> write "\""

inSingleQuotes :: PrinterOutput w m => m () -> m ()
inSingleQuotes thing = write "\'" >> thing >> write "\'"

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

instance PrettyPrint CharLiteral where
    prettyPrint flags s@(CharLiteral _) =
        betweenParentheses
            flags
            (  write "CharLiteral "
            >> inSingleQuotes (write (escapeCString [getCharLiteral s]))
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

instance PrettyPrint (UnifiedVariable Variable) where
    prettyPrint flags (ObjectVariable sv) =
        writeOneFieldStruct flags "ObjectVariable" sv
    prettyPrint flags (MetaVariable sv)   =
        writeOneFieldStruct flags "SortVariable" sv

instance PrettyPrint UnifiedPattern where
    prettyPrint flags (ObjectPattern sv) =
        writeOneFieldStruct flags "ObjectPattern" sv
    prettyPrint flags (MetaPattern sv)   =
        writeOneFieldStruct flags "MetaPattern" sv

instance (IsMeta a, PrettyPrint p) => PrettyPrint (And a p) where
    prettyPrint _ p@(And _ _ _) =
        writeStructure
            "And"
            [ writeFieldNewLine "andSort" andSort p
            , writeFieldNewLine "andFirst" andFirst p
            , writeFieldNewLine "andSecond" andSecond p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Application a p) where
    prettyPrint _ p@(Application _ _) =
        writeStructure
            "Application"
            [ writeFieldNewLine
                "applicationSymbolOrAlias" applicationSymbolOrAlias p
            , writeListField "applicationChildren" applicationChildren p
            ]

instance (IsMeta a) => PrettyPrint (Bottom a p) where
    prettyPrint flags (Bottom p) =
        writeOneFieldStruct flags "Bottom" p

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Ceil a p) where
    prettyPrint _ p@(Ceil _ _ _) =
        writeStructure
            "Ceil"
            [ writeFieldNewLine "ceilOperandSort" ceilOperandSort p
            , writeFieldNewLine "ceilResultSort" ceilResultSort p
            , writeFieldNewLine "ceilChild" ceilChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Equals a p) where
    prettyPrint _ p@(Equals _ _ _ _) =
        writeStructure
            "Equals"
            [ writeFieldNewLine "equalsOperandSort" equalsOperandSort p
            , writeFieldNewLine "equalsResultSort" equalsResultSort p
            , writeFieldNewLine "equalsFirst" equalsFirst p
            , writeFieldNewLine "equalsSecond" equalsSecond p
            ]

instance (IsMeta a, PrettyPrint p, PrettyPrint (v a))
    => PrettyPrint (Exists a v p) where
    prettyPrint _ p@(Exists _ _ _) =
        writeStructure
            "Exists"
            [ writeFieldNewLine "existsSort" existsSort p
            , writeFieldNewLine "existsVariable" existsVariable p
            , writeFieldNewLine "existsChild" existsChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Floor a p) where
    prettyPrint _ p@(Floor _ _ _) =
        writeStructure
            "Floor"
            [ writeFieldNewLine "floorOperandSort" floorOperandSort p
            , writeFieldNewLine "floorResultSort" floorResultSort p
            , writeFieldNewLine "floorChild" floorChild p
            ]

instance (IsMeta a, PrettyPrint p, PrettyPrint (v a))
    => PrettyPrint (Forall a v p) where
    prettyPrint _ p@(Forall _ _ _) =
        writeStructure
            "Forall"
            [ writeFieldNewLine "forallSort" forallSort p
            , writeFieldNewLine "forallVariable" forallVariable p
            , writeFieldNewLine "forallChild" forallChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Iff a p) where
    prettyPrint _ p@(Iff _ _ _) =
        writeStructure
            "Iff"
            [ writeFieldNewLine "iffSort" iffSort p
            , writeFieldNewLine "iffFirst" iffFirst p
            , writeFieldNewLine "iffSecond" iffSecond p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Implies a p) where
    prettyPrint _ p@(Implies _ _ _) =
        writeStructure
            "Implies"
            [ writeFieldNewLine "impliesSort" impliesSort p
            , writeFieldNewLine "impliesFirst" impliesFirst p
            , writeFieldNewLine "impliesSecond" impliesSecond p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (In a p) where
    prettyPrint _ p@(In _ _ _ _) =
        writeStructure
            "In"
            [ writeFieldNewLine "inOperandSort" inOperandSort p
            , writeFieldNewLine "inResultSort" inResultSort p
            , writeFieldNewLine "inContainedChild" inContainedChild p
            , writeFieldNewLine "inContainingChild" inContainingChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Next a p) where
    prettyPrint _ p@(Next _ _) =
        writeStructure
            "Next"
            [ writeFieldNewLine "nextSort" nextSort p
            , writeFieldNewLine "nextChild" nextChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Not a p) where
    prettyPrint _ p@(Not _ _) =
        writeStructure
            "Not"
            [ writeFieldNewLine "notSort" notSort p
            , writeFieldNewLine "notChild" notChild p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Or a p) where
    prettyPrint _ p@(Or _ _ _) =
        writeStructure
            "Or"
            [ writeFieldNewLine "orSort" orSort p
            , writeFieldNewLine "orFirst" orFirst p
            , writeFieldNewLine "orSecond" orSecond p
            ]

instance (IsMeta a, PrettyPrint p) => PrettyPrint (Rewrites a p) where
    prettyPrint _ p@(Rewrites _ _ _) =
        writeStructure
            "Rewrites"
            [ writeFieldNewLine "rewritesSort" rewritesSort p
            , writeFieldNewLine "rewritesFirst" rewritesFirst p
            , writeFieldNewLine "rewritesSecond" rewritesSecond p
            ]

instance (IsMeta a) => PrettyPrint (Top a p) where
    prettyPrint flags (Top p) =
        writeOneFieldStruct flags "Top" p

instance (IsMeta a, PrettyPrint p, PrettyPrint (v a),
          PrettyPrint (UnifiedVariable v))
    => PrettyPrint (Pattern a v p) where
    prettyPrint flags (AndPattern p) =
        writeOneFieldStruct flags "AndPattern" p
    prettyPrint flags (ApplicationPattern p)   =
        writeOneFieldStruct flags "ApplicationPattern" p
    prettyPrint flags (BottomPattern p)        =
        writeOneFieldStruct flags "BottomPattern" p
    prettyPrint flags (CeilPattern p)          =
        writeOneFieldStruct flags "CeilPattern" p
    prettyPrint flags (EqualsPattern p)        =
        writeOneFieldStruct flags "EqualsPattern" p
    prettyPrint flags (ExistsPattern p)        =
        writeOneFieldStruct flags "ExistsPattern" p
    prettyPrint flags (FloorPattern p)         =
        writeOneFieldStruct flags "FloorPattern" p
    prettyPrint flags (ForallPattern p)        =
        writeOneFieldStruct flags "ForallPattern" p
    prettyPrint flags (IffPattern p)           =
        writeOneFieldStruct flags "IffPattern" p
    prettyPrint flags (ImpliesPattern p)       =
        writeOneFieldStruct flags "ImpliesPattern" p
    prettyPrint flags (InPattern p)            =
        writeOneFieldStruct flags "InPattern" p
    prettyPrint flags (NextPattern p)          =
        writeOneFieldStruct flags "NextPattern" p
    prettyPrint flags (NotPattern p)           =
        writeOneFieldStruct flags "NotPattern" p
    prettyPrint flags (OrPattern p)            =
        writeOneFieldStruct flags "OrPattern" p
    prettyPrint flags (RewritesPattern p)      =
        writeOneFieldStruct flags "RewritesPattern" p
    prettyPrint flags (StringLiteralPattern p) =
        writeOneFieldStruct flags "StringLiteralPattern" p
    prettyPrint flags (CharLiteralPattern p) =
        writeOneFieldStruct flags "CharLiteralPattern" p
    prettyPrint flags (TopPattern p)           =
        writeOneFieldStruct flags "TopPattern" p
    prettyPrint flags (VariablePattern p)      =
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
                "sentenceAliasReturnSort" sentenceAliasResultSort sa
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
                "sentenceSymbolReturnSort" sentenceSymbolResultSort sa
            , writeAttributesField
                "sentenceSymbolAttributes" (sentenceSymbolAttributes sa)
            ]

instance PrettyPrint SentenceImport where
    prettyPrint _ sa@(SentenceImport _ _) =
        writeStructure
            "SentenceImport"
            [ writeFieldNewLine
                "sentenceImportModuleName" sentenceImportModuleName sa
            , writeAttributesField
                "sentenceAxiomAttributes" (sentenceImportAttributes sa)
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
    prettyPrint flags (SentenceImportSentence s)        =
        writeOneFieldStruct flags "SentenceImportSentence" s
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
            , writeListField "definitionModules" definitionModules d
            ]
