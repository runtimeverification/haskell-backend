module Kore.ASTPrettyPrint
    ( prettyPrintToString
    , PrettyPrint(..)
    , Flags(..)
    ) where

import Data.Functor.Foldable
import Data.List
       ( intersperse )

import Data.Functor.Impredicative
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.Parser.CString
       ( escapeCString )
import Kore.Unification.Unifier

import Data.String(fromString)
import Data.Text.Prettyprint.Doc as Doc
import Data.Text.Prettyprint.Doc.Render.String

{-# ANN module ("HLint: ignore Use record patterns" :: String) #-}
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
    prettyPrint :: Flags -> a -> Doc ann

prettyPrintToString :: PrettyPrint a => a -> String
prettyPrintToString a = renderString (layoutPretty options doc)
  where
    doc = prettyPrint MaySkipParentheses a
    options = defaultLayoutOptions { layoutPageWidth = Unbounded }

{- utility functions -}

betweenParentheses :: Flags -> Doc ann -> Doc ann
betweenParentheses NeedsParentheses thing = parens thing
betweenParentheses MaySkipParentheses thing = thing

writeOneFieldStruct
    :: (PrettyPrint a)
    => Flags -> String -> a -> Doc ann
writeOneFieldStruct flags name content =
    writeOneFieldStructK flags name (prettyPrint NeedsParentheses content)

writeTwoFieldStruct
    :: (PrettyPrint a, PrettyPrint b)
    => Flags -> String -> a -> b -> Doc ann
writeTwoFieldStruct flags name contenta contentb =
    writeOneFieldStructK
        flags
        name
        (   prettyPrint NeedsParentheses contenta
        <+> prettyPrint NeedsParentheses contentb
        )

writeThreeFieldStruct
    :: (PrettyPrint a, PrettyPrint b, PrettyPrint c)
    => Flags -> String -> a -> b -> c -> Doc ann
writeThreeFieldStruct flags name contenta contentb contentc =
    writeOneFieldStructK
        flags
        name
        (   prettyPrint NeedsParentheses contenta
        <+> prettyPrint NeedsParentheses contentb
        <+> prettyPrint NeedsParentheses contentc
        )

writeOneFieldStructK
    :: Flags -> String -> Doc ann -> Doc ann
writeOneFieldStructK flags name fieldWriterAction =
    betweenParentheses
        flags
        (fromString name <+> fieldWriterAction)

writeFieldOneLine
    :: (PrettyPrint a) => String -> (b -> a) -> b -> Doc ann
writeFieldOneLine fieldName field object =
    fromString fieldName
    <+> "="
    <+> prettyPrint MaySkipParentheses (field object)

writeListField
    :: (PrettyPrint a) => String -> (b -> a) -> b -> Doc ann
writeListField fieldName field object =
    fromString fieldName
    <+> "=" <> prettyPrint MaySkipParentheses (field object)

writeFieldNewLine
    :: (PrettyPrint a) => String -> (b -> a) -> b -> Doc ann
writeFieldNewLine fieldName field object =
    fromString fieldName
    <+> "="
    <> nest 4
        (Doc.line <> prettyPrint MaySkipParentheses (field object))

writeAttributesField
    :: String
    -> Attributes
    -> Doc ann
writeAttributesField fieldName attributes@(Attributes as) =
    fromString fieldName
    <+> "=" <>
    if null as
        then space <> prettyPrint MaySkipParentheses attributes
        else
            nest 4
                (Doc.line <> prettyPrint MaySkipParentheses attributes)

writeStructure :: String -> [Doc ann] -> Doc ann
writeStructure name fields =
    fromString name <> inCurlyBracesIndent (printableList fields)

printableList :: [Doc ann] -> [Doc ann]
printableList = intersperse (Doc.line <> comma <> space)

instance MetaOrObject level => PrettyPrint (Id level) where
    prettyPrint flags id'@(Id _ _) =
        betweenParentheses
            flags
            ("(Id \""
            <> fromString (getId id')
                -- TODO(virgil): use flags to qualify id only if necessary
            <> "\" AstLocationNone) :: Id "
            <> viaShow (isMetaOrObject id')
            )

instance
    (PrettyPrint (a Meta), PrettyPrint (a Object))
    => PrettyPrint (Unified a)
  where
    prettyPrint flags (UnifiedMeta x) =
        writeOneFieldStruct flags "UnifiedMeta" x
    prettyPrint flags (UnifiedObject x) =
        writeOneFieldStruct flags "UnifiedObject" x

instance PrettyPrint a => PrettyPrint [a] where
    prettyPrint _ items =
        inSquareBracketsIndent
            (printableList (map (prettyPrint MaySkipParentheses) items))

listWithDelimiters :: String -> String -> [Doc ann] -> Doc ann
listWithDelimiters start end [] =
    " " <> fromString start <> fromString end
listWithDelimiters start end items =
    nest 4 $
        Doc.line
        <> fromString start
        <+> hcat items
        <> Doc.line
        <> fromString end

inCurlyBracesIndent :: [Doc ann] -> Doc ann
inCurlyBracesIndent = listWithDelimiters "{" "}"

inSquareBracketsIndent :: [Doc ann] -> Doc ann
inSquareBracketsIndent = listWithDelimiters "[" "]"

inDoubleQuotes :: Doc ann -> Doc ann
inDoubleQuotes thing = "\"" <> thing <> "\""

inSingleQuotes :: Doc ann -> Doc ann
inSingleQuotes thing = "\'" <> thing <> "\'"

instance MetaOrObject level => PrettyPrint (SortVariable level) where
    prettyPrint flags sv =
        writeOneFieldStruct flags "SortVariable" (getSortVariable sv)

instance MetaOrObject level => PrettyPrint (Sort level) where
    prettyPrint flags (SortVariableSort sv) =
        writeOneFieldStruct flags "SortVariableSort" sv
    prettyPrint flags (SortActualSort sa)   =
        writeOneFieldStruct flags "SortActualSort" sa

instance MetaOrObject level => PrettyPrint (SortActual level) where
    prettyPrint _ sa@(SortActual _ _) =
        writeStructure "SortActual"
            [ writeFieldOneLine "sortActualName" sortActualName sa
            , writeListField "sortActualSorts" sortActualSorts sa
            ]

instance PrettyPrint StringLiteral where
    prettyPrint flags s@(StringLiteral _) =
        betweenParentheses
            flags
            ("StringLiteral "
            <> inDoubleQuotes (fromString (escapeCString (getStringLiteral s)))
            )

instance PrettyPrint CharLiteral where
    prettyPrint flags s@(CharLiteral _) =
        betweenParentheses
            flags
            ("CharLiteral "
            <> inSingleQuotes (fromString (escapeCString [getCharLiteral s]))
            )

instance MetaOrObject level => PrettyPrint (SymbolOrAlias level) where
    prettyPrint _ s@(SymbolOrAlias _ _) =
        writeStructure "SymbolOrAlias"
            [ writeFieldOneLine
                "symbolOrAliasConstructor" symbolOrAliasConstructor s
            , writeListField "symbolOrAliasParams" symbolOrAliasParams s
            ]

instance MetaOrObject level => PrettyPrint (Alias level) where
    prettyPrint _ s@(Alias _ _) =
        writeStructure "Alias"
            [ writeFieldOneLine "aliasConstructor" aliasConstructor s
            , writeListField "aliasParams" aliasParams s
            ]

instance MetaOrObject level => PrettyPrint (Symbol level) where
    prettyPrint _ s@(Symbol _ _) =
        writeStructure "Symbol"
            [ writeFieldOneLine "symbolConstructor" symbolConstructor s
            , writeListField "symbolParams" symbolParams s
            ]

instance PrettyPrint ModuleName where
    prettyPrint flags s@(ModuleName _) =
        betweenParentheses
            flags
            ( "ModuleName "
            <> inDoubleQuotes (fromString (getModuleName s))
            )

instance MetaOrObject level => PrettyPrint (Variable level) where
    prettyPrint _ var@(Variable _ _) =
        writeStructure "Variable"
            [ writeFieldOneLine "variableName" variableName var
            , writeFieldNewLine "variableSort" variableSort var
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (And level child)
  where
    prettyPrint _ p@(And _ _ _) =
        writeStructure
            "And"
            [ writeFieldNewLine "andSort" andSort p
            , writeFieldNewLine "andFirst" andFirst p
            , writeFieldNewLine "andSecond" andSecond p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Application level child)
  where
    prettyPrint _ p@(Application _ _) =
        writeStructure
            "Application"
            [ writeFieldNewLine
                "applicationSymbolOrAlias" applicationSymbolOrAlias p
            , writeListField "applicationChildren" applicationChildren p
            ]

instance MetaOrObject level => PrettyPrint (Bottom level child) where
    prettyPrint flags (Bottom p) =
        writeOneFieldStruct flags "Bottom" p

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Ceil level child)
  where
    prettyPrint _ p@(Ceil _ _ _) =
        writeStructure
            "Ceil"
            [ writeFieldNewLine "ceilOperandSort" ceilOperandSort p
            , writeFieldNewLine "ceilResultSort" ceilResultSort p
            , writeFieldNewLine "ceilChild" ceilChild p
            ]

instance
    ( MetaOrObject level
    ) => PrettyPrint (DomainValue level (Fix (Pattern Meta Variable))) where
    prettyPrint _ p@(DomainValue _ _) =
        writeStructure
            "DomainValue"
            [ writeFieldNewLine "domainValueSort" domainValueSort p
            , writeFieldNewLine "domainValueChild" domainValueChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Equals level child)
  where
    prettyPrint _ p@(Equals _ _ _ _) =
        writeStructure
            "Equals"
            [ writeFieldNewLine "equalsOperandSort" equalsOperandSort p
            , writeFieldNewLine "equalsResultSort" equalsResultSort p
            , writeFieldNewLine "equalsFirst" equalsFirst p
            , writeFieldNewLine "equalsSecond" equalsSecond p
            ]

instance
    ( PrettyPrint child
    , PrettyPrint (variable level)
    , MetaOrObject level
    ) => PrettyPrint (Exists level variable child)
  where
    prettyPrint _ p@(Exists _ _ _) =
        writeStructure
            "Exists"
            [ writeFieldNewLine "existsSort" existsSort p
            , writeFieldNewLine "existsVariable" existsVariable p
            , writeFieldNewLine "existsChild" existsChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Floor level child)
  where
    prettyPrint _ p@(Floor _ _ _) =
        writeStructure
            "Floor"
            [ writeFieldNewLine "floorOperandSort" floorOperandSort p
            , writeFieldNewLine "floorResultSort" floorResultSort p
            , writeFieldNewLine "floorChild" floorChild p
            ]

instance
    ( PrettyPrint child
    , PrettyPrint (variable level)
    , MetaOrObject level
    ) => PrettyPrint (Forall level variable child) where
    prettyPrint _ p@(Forall _ _ _) =
        writeStructure
            "Forall"
            [ writeFieldNewLine "forallSort" forallSort p
            , writeFieldNewLine "forallVariable" forallVariable p
            , writeFieldNewLine "forallChild" forallChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Iff level child)
  where
    prettyPrint _ p@(Iff _ _ _) =
        writeStructure
            "Iff"
            [ writeFieldNewLine "iffSort" iffSort p
            , writeFieldNewLine "iffFirst" iffFirst p
            , writeFieldNewLine "iffSecond" iffSecond p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Implies level child)
  where
    prettyPrint _ p@(Implies _ _ _) =
        writeStructure
            "Implies"
            [ writeFieldNewLine "impliesSort" impliesSort p
            , writeFieldNewLine "impliesFirst" impliesFirst p
            , writeFieldNewLine "impliesSecond" impliesSecond p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (In level child)
  where
    prettyPrint _ p@(In _ _ _ _) =
        writeStructure
            "In"
            [ writeFieldNewLine "inOperandSort" inOperandSort p
            , writeFieldNewLine "inResultSort" inResultSort p
            , writeFieldNewLine "inContainedChild" inContainedChild p
            , writeFieldNewLine "inContainingChild" inContainingChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Next level child)
  where
    prettyPrint _ p@(Next _ _) =
        writeStructure
            "Next"
            [ writeFieldNewLine "nextSort" nextSort p
            , writeFieldNewLine "nextChild" nextChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Not level child)
  where
    prettyPrint _ p@(Not _ _) =
        writeStructure
            "Not"
            [ writeFieldNewLine "notSort" notSort p
            , writeFieldNewLine "notChild" notChild p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Or level child)
  where
    prettyPrint _ p@(Or _ _ _) =
        writeStructure
            "Or"
            [ writeFieldNewLine "orSort" orSort p
            , writeFieldNewLine "orFirst" orFirst p
            , writeFieldNewLine "orSecond" orSecond p
            ]

instance
    ( PrettyPrint child
    , MetaOrObject level
    ) => PrettyPrint (Rewrites level child)
  where
    prettyPrint _ p@(Rewrites _ _ _) =
        writeStructure
            "Rewrites"
            [ writeFieldNewLine "rewritesSort" rewritesSort p
            , writeFieldNewLine "rewritesFirst" rewritesFirst p
            , writeFieldNewLine "rewritesSecond" rewritesSecond p
            ]

instance MetaOrObject level => PrettyPrint (Top level child) where
    prettyPrint flags (Top p) =
        writeOneFieldStruct flags "Top" p

instance
    ( PrettyPrint child
    , PrettyPrint (variable level)
    , MetaOrObject level
    ) => PrettyPrint (Pattern level variable child)
  where
    prettyPrint flags (AndPattern p) =
        writeOneFieldStruct flags "AndPattern" p
    prettyPrint flags (ApplicationPattern p)   =
        writeOneFieldStruct flags "ApplicationPattern" p
    prettyPrint flags (BottomPattern p)        =
        writeOneFieldStruct flags "BottomPattern" p
    prettyPrint flags (CeilPattern p)          =
        writeOneFieldStruct flags "CeilPattern" p
    prettyPrint flags (DomainValuePattern p)          =
        writeOneFieldStruct flags "DomainValuePattern" p
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

instance PrettyPrint CommonKorePattern where
    prettyPrint flags korePattern =
        writeOneFieldStructK flags "Fix"
        $ writeOneFieldStructK NeedsParentheses "UnifiedPattern"
        $ case getUnifiedPattern (project korePattern) of
            UnifiedMeta p ->
                writeOneFieldStructK NeedsParentheses "UnifiedMeta"
                $ writeOneFieldStruct NeedsParentheses "Rotate31" (unRotate31 p)
            UnifiedObject p ->
                writeOneFieldStructK NeedsParentheses "UnifiedObject"
                $ writeOneFieldStruct NeedsParentheses "Rotate31" (unRotate31 p)

instance (MetaOrObject level, PrettyPrint (variable level))
    => PrettyPrint (PureMLPattern level variable)
  where
    prettyPrint flags purePattern =
        writeOneFieldStruct flags "Fix" (project purePattern)

instance PrettyPrint Attributes
  where
    prettyPrint flags (Attributes a)
        | null a    = "Attributes []"
        | otherwise = writeOneFieldStruct flags "Attributes" a

instance
    ( MetaOrObject level
    , PrettyPrint (Fix (pat variable))
    , PrettyPrint (variable level)
    ) => PrettyPrint (SentenceAlias level pat variable)
  where
    prettyPrint _ sa@(SentenceAlias _ _ _ _ _ _) =
        writeStructure
            "SentenceAlias"
            [ writeFieldNewLine "sentenceAliasAlias" sentenceAliasAlias sa
            , writeListField "sentenceAliasSorts" sentenceAliasSorts sa
            , writeFieldNewLine
                "sentenceAliasReturnSort" sentenceAliasResultSort sa
            , writeFieldNewLine "sentenceAliasLeftPattern" sentenceAliasLeftPattern sa
            , writeFieldNewLine "sentenceAliasRightPattern" sentenceAliasRightPattern sa
            , writeAttributesField
                "sentenceAliasAttributes" (sentenceAliasAttributes sa)
            ]

instance
    ( MetaOrObject level
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (SentenceSymbol level pat variable)
  where
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

instance
    (PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (SentenceImport pat variable)
  where
    prettyPrint _ sa@(SentenceImport _ _) =
        writeStructure
            "SentenceImport"
            [ writeFieldNewLine
                "sentenceImportModuleName" sentenceImportModuleName sa
            , writeAttributesField
                "sentenceAxiomAttributes" (sentenceImportAttributes sa)
            ]

instance
    ( PrettyPrint sortParam
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (SentenceAxiom sortParam pat variable)
  where
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

instance
    ( MetaOrObject level
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (SentenceSort level pat variable)
  where
    prettyPrint _ sa@(SentenceSort _ _ _) =
        writeStructure
            "SentenceSort"
            [ writeFieldOneLine "sentenceSortName" sentenceSortName sa
            , writeListField
                "sentenceSortParameters" sentenceSortParameters sa
            , writeAttributesField
                "sentenceSortAttributes" (sentenceSortAttributes sa)
            ]

instance
    ( MetaOrObject level
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (SentenceHook level pat variable)
  where
    prettyPrint flags (SentenceHookedSymbol s)   =
        writeOneFieldStruct flags "SentenceHookedSymbol" s
    prettyPrint flags (SentenceHookedSort s)         =
        writeOneFieldStruct flags "SentenceHookedSort" s

instance
    ( MetaOrObject level
    , PrettyPrint sortParam
    , PrettyPrint (Fix (pat variable))
    , PrettyPrint (variable level)
    ) => PrettyPrint (Sentence level sortParam pat variable)
  where
    prettyPrint flags (SentenceAliasSentence s)    =
        writeOneFieldStruct flags "SentenceAliasSentence" s
    prettyPrint flags (SentenceSymbolSentence s)   =
        writeOneFieldStruct flags "SentenceSymbolSentence" s
    prettyPrint flags (SentenceImportSentence s)        =
        writeOneFieldStruct flags "SentenceImportSentence" s
    prettyPrint flags (SentenceAxiomSentence s)        =
        writeOneFieldStruct flags "SentenceAxiomSentence" s
    prettyPrint flags (SentenceSortSentence s)         =
        writeOneFieldStruct flags "SentenceSortSentence" s
    prettyPrint flags (SentenceHookSentence s)         =
        writeOneFieldStruct flags "SentenceHookSentence" s

instance
    ( PrettyPrint sortParam
    , PrettyPrint (Fix (pat variable))
    , PrettyPrint (variable Object)
    , PrettyPrint (variable Meta)
    ) => PrettyPrint (UnifiedSentence sortParam pat variable)
  where
    prettyPrint flags (UnifiedSentence (UnifiedMeta rs)) =
        writeOneFieldStruct flags "MetaSentence" (unRotate41 rs)
    prettyPrint flags (UnifiedSentence (UnifiedObject rs)) =
        writeOneFieldStruct flags "ObjectSentence" (unRotate41 rs)

instance
    (PrettyPrint (sentence sortParam pat variable)
    , PrettyPrint sortParam
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (Module sentence sortParam pat variable)
  where
    prettyPrint _ m@(Module _ _ _) =
        writeStructure
            "Module"
            [ writeFieldOneLine "moduleName" moduleName m
            , writeListField "moduleSentences" moduleSentences m
            , writeAttributesField "moduleAttributes" (moduleAttributes m)
            ]

instance
    (PrettyPrint (sentence sortParam pat variable)
    , PrettyPrint sortParam
    , PrettyPrint (Fix (pat variable))
    ) => PrettyPrint (Definition sentence sortParam pat variable)
  where
    prettyPrint _ d@(Definition _ _) =
        writeStructure
            "Definition"
            [ writeAttributesField
                "definitionAttributes" (definitionAttributes d)
            , writeListField "definitionModules" definitionModules d
            ]

instance PrettyPrint a => PrettyPrint (Maybe a) where
    prettyPrint flags (Just x) =
        writeOneFieldStruct flags "Just" x
    prettyPrint _ Nothing = "Nothing"

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
    prettyPrint flags (Left x) =
        writeOneFieldStruct flags "Left" x
    prettyPrint flags (Right x) =
        writeOneFieldStruct flags "Right" x

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a, b) where
    prettyPrint _ (x, y) =
        listWithDelimiters "(" ")"
            (printableList
                [ prettyPrint MaySkipParentheses x
                , prettyPrint MaySkipParentheses y
                ])

instance (MetaOrObject level, PrettyPrint (variable level))
    => PrettyPrint (UnificationSolution level variable)
  where
    prettyPrint _ us@(UnificationSolution _ _) =
        writeStructure
            "UnificationSolution"
            [ writeFieldNewLine
                "unificationSolutionTerm" unificationSolutionTerm us
            , writeListField
                "unificationSolutionConstraints"
                unificationSolutionConstraints
                us
            ]

-- TODO: when refactoring these, consider removing `writeTwoFieldStruct`
-- TODO: when refactoring these, consider removing `writeThreeFieldStruct`
instance (MetaOrObject level, PrettyPrint (variable level))
    => PrettyPrint (UnificationProof level variable)
  where
    prettyPrint _ EmptyUnificationProof = "EmptyUnificationProof"
    prettyPrint flags (CombinedUnificationProof p) =
        writeOneFieldStruct flags "CombinedUnificationProof" p
    prettyPrint flags (ConjunctionIdempotency p) =
        writeOneFieldStruct flags "ConjunctionIdempotency" p
    prettyPrint flags (AndDistributionAndConstraintLifting patternHead proofs) =
        writeTwoFieldStruct
            flags
            "AndDistributionAndConstraintLifting"
            patternHead
            proofs
    prettyPrint flags (Proposition_5_24_3 funProof var pat) =
        writeThreeFieldStruct flags "Proposition_5_24_3" funProof var pat
    prettyPrint flags (SubstitutionMerge var pat1 pat2) =
        writeThreeFieldStruct flags "SubstitutionMerge" var pat1 pat2

-- TODO: when refactoring these, consider removing `writeTwoFieldStruct`
instance MetaOrObject level => PrettyPrint (UnificationError level) where
    prettyPrint flags (ConstructorClash h1 h2) =
        writeTwoFieldStruct flags "ConstructorClash" h1 h2
    prettyPrint flags (SortClash s1 s2) =
        writeTwoFieldStruct flags "SortClash" s1 s2
    prettyPrint flags (NonConstructorHead h) =
        writeOneFieldStruct flags "NonConstructorHead" h
    prettyPrint flags (NonFunctionalHead h) =
        writeOneFieldStruct flags "NonFunctionalHead" h
    prettyPrint _ NonFunctionalPattern = "NonFunctionalPattern"
    prettyPrint _ UnsupportedPatterns = "UnsupportedPatterns"
    prettyPrint _ EmptyPatternList = "EmptyPatternList"

instance (MetaOrObject level, PrettyPrint (variable level))
    => PrettyPrint (FunctionalProof level variable)
  where
    prettyPrint flags (FunctionalVariable v) =
        writeOneFieldStruct flags "FunctionalVariable" v
    prettyPrint flags (FunctionalHead h) =
        writeOneFieldStruct flags "FunctionalHead" h
