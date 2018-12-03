{-|
Module      : Kore.Unparser
Description : Render abstract to concrete Kore syntax
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unparser
    ( Unparse (..)
    , unparseToString
    , layoutPrettyUnbounded
    ) where

import           Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import           Data.Maybe
                 ( catMaybes )
import           Data.String
                 ( IsString (fromString) )
import           Data.Text.Prettyprint.Doc hiding
                 ( list )
import           Data.Text.Prettyprint.Doc.Render.String
                 ( renderString )
import           Data.Void

import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Domain.External as Domain
import           Kore.Parser.CString
                 ( escapeCString )

{- | Class of types that can be rendered in concrete Kore syntax.

    @Unparse@ should only be instantiated for types with a corresponding
    concrete syntax, i.e. each instance of @Unparse@ should correspond to a
    parser in "Kore.Parser.Parser".

    @Unparse@ assumes that the pattern is fully externalized by
    'Builtin.externalizePattern'. An error will be thrown if an internal domain
    value is found.

 -}
class Unparse p where
    -- | Render a type from abstract to concrete Kore syntax.
    unparse :: p -> Doc ann

-- | Serialize an object to 'String'.
unparseToString :: Unparse p => p -> String
unparseToString =
    renderString . layoutPretty defaultLayoutOptions . unparse

instance Unparse (Id level) where
    unparse = pretty . getId

instance Unparse StringLiteral where
    unparse = dquotes . fromString . escapeCString . getStringLiteral

instance Unparse CharLiteral where
    unparse = squotes . fromString . escapeCString . (: []) . getCharLiteral

instance Unparse (SymbolOrAlias level) where
    unparse
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            }
      =
        unparse symbolOrAliasConstructor <> parameters symbolOrAliasParams

instance Unparse (Symbol level) where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor
        <> parameters symbolParams

instance Unparse (Alias level) where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor
        <> parameters aliasParams

instance Unparse (SortVariable level) where
    unparse = unparse . getSortVariable

instance Unparse (SortActual level) where
    unparse SortActual { sortActualName, sortActualSorts } =
        unparse sortActualName <> parameters sortActualSorts

instance Unparse (Sort level) where
    unparse =
        \case
            SortVariableSort sortVariable -> unparse sortVariable
            SortActualSort sortActual -> unparse sortActual

instance Unparse (Concrete level) where
    unparse = \case {}

instance Unparse (Variable level) where
    unparse Variable { variableName, variableSort } =
        unparse variableName <> colon <> unparse variableSort

instance Unparse MLPatternType where
    unparse = ("\\" <>) . fromString . patternString

instance Unparse child => Unparse (And level child) where
    unparse
        And { andSort, andFirst, andSecond }
      =
        "\\and"
        <> parameters [andSort]
        <> arguments [andFirst, andSecond]

instance Unparse child => Unparse (Application level child) where
    unparse
        Application { applicationSymbolOrAlias, applicationChildren }
      =
        unparse applicationSymbolOrAlias
        <> arguments applicationChildren

instance Unparse (Bottom level child) where
    unparse Bottom { bottomSort } =
        "\\bottom" <> parameters [bottomSort] <> noArguments

instance Unparse child => Unparse (Ceil level child) where
    unparse Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        "\\ceil"
        <> parameters [ceilOperandSort, ceilResultSort]
        <> arguments [ceilChild]

instance
    (Unparse (domain child), level ~ Object) =>
    Unparse (DomainValue level domain child)
  where
    unparse DomainValue { domainValueSort, domainValueChild } =
        "\\dv"
        <> parameters [domainValueSort]
        <> arguments' [unparse domainValueChild]
      where

instance
    Unparse a => Unparse (Const a child)
  where
    unparse (Const a) = unparse a

instance Unparse Void where
    unparse = \case {}

instance
    Unparse child => Unparse (Domain.Builtin child)
  where
    unparse =
        \case
            Domain.BuiltinPattern child -> unparse child
            Domain.BuiltinMap _ -> Builtin.notImplementedInternal
            Domain.BuiltinList _ -> Builtin.notImplementedInternal
            Domain.BuiltinSet _ -> Builtin.notImplementedInternal

instance Unparse (Domain.External child) where
    unparse (Domain.External lit) = unparse lit

instance Unparse child => Unparse (Equals level child) where
    unparse
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        "\\equals"
        <> parameters [equalsOperandSort, equalsResultSort]
        <> arguments [equalsFirst, equalsSecond]

instance
    ( Unparse child
    , Unparse (variable level)
    ) =>
    Unparse (Exists level variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

instance Unparse child => Unparse (Floor level child) where
    unparse Floor { floorOperandSort, floorResultSort, floorChild } =
        "\\floor"
        <> parameters [floorOperandSort, floorResultSort]
        <> arguments [floorChild]

instance
    ( Unparse child
    , Unparse (variable level)
    ) =>
    Unparse (Forall level variable child)
  where
    unparse Forall { forallSort, forallVariable, forallChild } =
        "\\forall"
        <> parameters [forallSort]
        <> arguments' [unparse forallVariable, unparse forallChild]

instance Unparse child => Unparse (Iff level child) where
    unparse Iff { iffSort, iffFirst, iffSecond } =
        "\\iff"
        <> parameters [iffSort]
        <> arguments [iffFirst, iffSecond]

instance Unparse child => Unparse (Implies level child) where
    unparse Implies { impliesSort, impliesFirst, impliesSecond } =
        "\\implies"
        <> parameters [impliesSort]
        <> arguments [impliesFirst, impliesSecond]

instance Unparse child => Unparse (In level child) where
    unparse
        In
            { inOperandSort
            , inResultSort
            , inContainedChild
            , inContainingChild
            }
      =
        "\\in"
        <> parameters [inOperandSort, inResultSort]
        <> arguments [inContainedChild, inContainingChild]

instance Unparse child => Unparse (Next level child) where
    unparse Next { nextSort, nextChild } =
        "\\next"
        <> parameters [nextSort]
        <> arguments [nextChild]

instance Unparse child => Unparse (Not level child) where
    unparse Not { notSort, notChild } =
        "\\not"
        <> parameters [notSort]
        <> arguments [notChild]

instance Unparse child => Unparse (Or level child) where
    unparse Or { orSort, orFirst, orSecond } =
        "\\or"
        <> parameters [orSort]
        <> arguments [orFirst, orSecond]

instance Unparse child => Unparse (Rewrites level child) where
    unparse Rewrites { rewritesSort, rewritesFirst, rewritesSecond } =
        "\\rewrites"
        <> parameters [rewritesSort]
        <> arguments [rewritesFirst, rewritesSecond]

instance Unparse (Top level child) where
    unparse Top { topSort } =
        "\\top" <> parameters [topSort] <> noArguments

instance
    ( Unparse child
    , Unparse (domain child)
    , Unparse (variable level)
    ) =>
    Unparse (Pattern level domain variable child)
  where
    unparse =
        \case
            AndPattern p           -> unparse p
            ApplicationPattern p   -> unparse p
            BottomPattern p        -> unparse p
            CeilPattern p          -> unparse p
            DomainValuePattern p   -> unparse p
            EqualsPattern p        -> unparse p
            ExistsPattern p        -> unparse p
            FloorPattern p         -> unparse p
            ForallPattern p        -> unparse p
            IffPattern p           -> unparse p
            ImpliesPattern p       -> unparse p
            InPattern p            -> unparse p
            NextPattern p          -> unparse p
            NotPattern p           -> unparse p
            OrPattern p            -> unparse p
            RewritesPattern p      -> unparse p
            StringLiteralPattern p -> unparse p
            CharLiteralPattern p   -> unparse p
            TopPattern p           -> unparse p
            VariablePattern p      -> unparse p

instance
    ( Functor domain
    , Unparse (variable level)
    , Unparse (domain self)
    , self ~ PurePattern level domain variable annotation
    ) =>
    Unparse (PurePattern level domain variable annotation)
  where
    unparse (Recursive.project -> _ :< pat) = unparse pat

instance
    ( Functor domain
    , Unparse (variable Meta)
    , Unparse (variable Object)
    , Unparse (domain self)
    , self ~ KorePattern domain variable annotation
    ) =>
    Unparse (KorePattern domain variable annotation)
  where
    unparse (Recursive.project -> _ :< pat) = unparse pat

instance
    ( Unparse (variable Meta)
    , Unparse (variable Object)
    , Unparse (domain child)
    , Unparse child
    ) =>
    Unparse (UnifiedPattern domain variable child)
  where
    unparse =
        \case
            UnifiedMetaPattern pat -> unparse pat
            UnifiedObjectPattern pat -> unparse pat

instance Unparse Attributes where
    unparse = attributes . getAttributes

instance
    ( Unparse (variable level)
    , Unparse child
    , Unparse (domain child)
    , child ~ pat domain variable ()
    ) =>
    Unparse (SentenceAlias level pat domain variable)
  where
    unparse
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        fillSep
            [ "alias"
            , unparse sentenceAliasAlias <> arguments sentenceAliasSorts
            , ":"
            , unparse sentenceAliasResultSort
            , "where"
            , unparse sentenceAliasLeftPattern
            , ":="
            , unparse sentenceAliasRightPattern
            , unparse sentenceAliasAttributes
            ]

instance Unparse (SentenceSymbol level pat domain variable) where
    unparse
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
      =
        fillSep
            [ "symbol"
            , unparse sentenceSymbolSymbol <> arguments sentenceSymbolSorts
            , ":"
            , unparse sentenceSymbolResultSort
            , unparse sentenceSymbolAttributes
            ]

instance Unparse ModuleName where
    unparse = pretty . getModuleName

instance Unparse (SentenceImport pat domain variable) where
    unparse
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        fillSep
            [ "import", unparse sentenceImportModuleName
            , unparse sentenceImportAttributes
            ]

instance Unparse (SentenceSort level pat domain variable) where
    unparse
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }
      =
        fillSep
            [ "sort"
            , unparse sentenceSortName <> parameters sentenceSortParameters
            , unparse sentenceSortAttributes
            ]

instance
    ( Unparse (pat domain variable ())
    , Unparse sortParam
    ) =>
    Unparse (SentenceAxiom sortParam pat domain variable)
  where
    unparse
        SentenceAxiom
            { sentenceAxiomParameters
            , sentenceAxiomPattern
            , sentenceAxiomAttributes
            }
      =
        fillSep
            [ "axiom"
            , parameters sentenceAxiomParameters
            , unparse sentenceAxiomPattern
            , unparse sentenceAxiomAttributes
            ]

instance Unparse UnifiedSortVariable where
    unparse =
        \case
            UnifiedMeta sv -> unparse sv
            UnifiedObject sv -> unparse sv

instance
    ( Unparse (SentenceSort level pat domain variable)
    , Unparse (SentenceSymbol level pat domain variable)
    ) =>
    Unparse (SentenceHook level pat domain variable)
  where
    unparse =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse a
            SentenceHookedSymbol a -> "hooked-" <> unparse a

instance
    ( Unparse (SentenceAlias level pat domain variable)
    , Unparse (SentenceSymbol level pat domain variable)
    , Unparse (SentenceImport pat domain variable)
    , Unparse (SentenceAxiom sortParam pat domain variable)
    , Unparse (SentenceSort level pat domain variable)
    ) =>
    Unparse (Sentence level sortParam pat domain variable)
  where
     unparse =
        \case
            SentenceAliasSentence s -> unparse s
            SentenceSymbolSentence s -> unparse s
            SentenceImportSentence s -> unparse s
            SentenceAxiomSentence s -> unparse s
            SentenceClaimSentence s -> unparse s
            SentenceSortSentence s -> unparse s
            SentenceHookSentence s -> unparse s


instance
    ( Unparse (Sentence Meta sortParam pat domain variable)
    , Unparse (Sentence Object sortParam pat domain variable)
    ) =>
    Unparse (UnifiedSentence sortParam pat domain variable)
  where
    unparse =
        \case
            UnifiedMetaSentence sentence -> unparse sentence
            UnifiedObjectSentence sentence -> unparse sentence

instance
    Unparse (sentence sortParam pat domain variable) =>
    Unparse (Module sentence sortParam pat domain variable)
  where
    unparse
        Module { moduleName, moduleSentences, moduleAttributes }
      =
        (vsep . catMaybes)
            [ Just ("module" <+> unparse moduleName)
            , case moduleSentences of
                [] -> Nothing
                _ -> Just $ (indent 4 . vsep) (unparse <$> moduleSentences)
            , Just "endmodule"
            , Just (unparse moduleAttributes)
            ]

instance
    Unparse (sentence sortParam pat domain variable) =>
    Unparse (Definition sentence sortParam pat domain variable)
  where
    unparse Definition { definitionAttributes, definitionModules } =
        vsep (unparse definitionAttributes : map unparse definitionModules)

parameters :: Unparse p => [p] -> Doc ann
parameters = parameters' . map unparse

-- | Print a list of sort parameters.
parameters' :: [Doc ann] -> Doc ann
parameters' = list lbrace rbrace

arguments :: Unparse p => [p] -> Doc ann
arguments = arguments' . map unparse

-- | Print a list of documents as arguments.
arguments' :: [Doc ann] -> Doc ann
arguments' = list lparen rparen

-- | Print a list of no arguments.
noArguments :: Doc ann
noArguments = arguments' []

attributes :: Unparse p => [p] -> Doc ann
attributes = attributes' . map unparse

-- | Print a list of documents as attributes.
attributes' :: [Doc ann] -> Doc ann
attributes' = list lbracket rbracket

-- | Print a list of documents separated by commas in the preferred Kore format.
list
    :: Doc ann  -- ^ opening list delimiter
    -> Doc ann  -- ^ closing list delimiter
    -> [Doc ann]  -- ^ list items
    -> Doc ann
list left right =
    \case
        [] -> left <> right
        xs -> (group . (<> close) . nest 4 . (open <>) . vsep . punctuate between) xs
  where
    open = left <> line'
    close = line' <> right
    between = comma

-- | Render a 'Doc ann' with indentation and without extra line breaks.
layoutPrettyUnbounded :: Doc ann -> SimpleDocStream ann
layoutPrettyUnbounded = layoutPretty LayoutOptions { layoutPageWidth = Unbounded }
