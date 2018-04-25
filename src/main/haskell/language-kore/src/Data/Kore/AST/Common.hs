{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-|
Module      : Data.Kore.AST.Common
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see Data.Kore.AST.Kore for the unified
              ones).
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort Object' or 'Sort Meta')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Data.Kore.AST.Common
    ( module Data.Kore.AST.Common
    , module Data.Kore.AST.CommonBase
    ) where

import           Data.Kore.AST.CommonBase
import           Data.Kore.AST.Metadata
import           Data.Typeable            (Typeable)

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that the 'StringLiteralPattern' and 'CharLiteralPattern' should
be members only of 'Pattern Meta'.
-}
data Pattern level variable metadata child where
    AndPattern
        :: !(metadata (And level child)) -> Pattern level variable metadata child
    ApplicationPattern
        :: !(metadata (Application level child)) -> Pattern level variable metadata child
    BottomPattern
        :: !(metadata (Bottom level child)) -> Pattern level variable metadata child
    CeilPattern
        :: !(metadata (Ceil level child)) -> Pattern level variable metadata child
    DomainValuePattern
        :: !(metadata (DomainValue Object child)) -> Pattern Object variable metadata child
    EqualsPattern
        :: !(metadata (Equals level child)) -> Pattern level variable metadata child
    ExistsPattern
        :: !(metadata (Exists level variable child)) -> Pattern level variable metadata child
    FloorPattern
        :: !(metadata (Floor level child)) -> Pattern level variable metadata child
    ForallPattern
        :: !(metadata (Forall level variable child)) -> Pattern level variable metadata child
    IffPattern
        :: !(metadata (Iff level child)) -> Pattern level variable metadata child
    ImpliesPattern
        :: !(metadata (Implies level child)) -> Pattern level variable metadata child
    InPattern
        :: !(metadata (In level child)) -> Pattern level variable metadata child
    NextPattern
        :: !(metadata (Next Object child)) -> Pattern Object variable metadata child
    NotPattern
        :: !(metadata (Not level child)) -> Pattern level variable metadata child
    OrPattern
        :: !(metadata (Or level child)) -> Pattern level variable metadata child
    RewritesPattern
        :: !(metadata (Rewrites Object child)) -> Pattern Object variable metadata child
    StringLiteralPattern
        :: !(metadata StringLiteral) -> Pattern Meta variable metadata child
    CharLiteralPattern
        :: !(metadata CharLiteral) -> Pattern Meta variable metadata child
    TopPattern
        :: !(metadata (Top level child)) -> Pattern level variable metadata child
    VariablePattern
        :: !(metadata (variable level)) -> Pattern level variable metadata child
  deriving (Typeable)

deriving instance
    ( Eq child
    , Eq (variable level)
    , EqMetadata level variable child metadata
    ) => Eq (Pattern level variable metadata child)
deriving instance
    ( Show child
    , Show (variable level)
    , ShowMetadata level variable child metadata
    ) => Show (Pattern level variable metadata child)
-- TODO: Actually think about the derivations below.
deriving instance
    (Functor metadata)
    => Functor (Pattern level variable metadata)
deriving instance
    (Foldable metadata)
    => Foldable (Pattern level variable metadata)
deriving instance
    (Traversable metadata)
    => Traversable (Pattern level variable metadata)

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceAlias level pat variable = SentenceAlias
    { sentenceAliasAlias      :: !(Alias level)
    , sentenceAliasSorts      :: ![Sort level]
    , sentenceAliasResultSort :: !(Sort level)
    , sentenceAliasAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol level pat variable = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol level)
    , sentenceSymbolSorts      :: ![Sort level]
    , sentenceSymbolResultSort :: !(Sort level)
    , sentenceSymbolAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq, Ord)

{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceImport pat variable = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort level pat variable = SentenceSort
    { sentenceSortName       :: !(Id level)
    , sentenceSortParameters :: ![SortVariable level]
    , sentenceSortAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom sortParam pat variable = SentenceAxiom
    { sentenceAxiomParameters :: ![sortParam]
    , sentenceAxiomPattern    :: !(pat variable)
    , sentenceAxiomAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence level sortParam pat variable where
    SentenceAliasSentence
        :: !(SentenceAlias level pat variable)
        -> Sentence level sortParam pat variable
    SentenceSymbolSentence
        :: !(SentenceSymbol level pat variable)
        -> Sentence level sortParam pat variable
    SentenceImportSentence
        :: !(SentenceImport pat variable)
        -> Sentence Meta sortParam pat variable
    SentenceAxiomSentence
        :: !(SentenceAxiom sortParam pat variable)
        -> Sentence Meta sortParam pat variable
    SentenceSortSentence
        :: !(SentenceSort Object pat variable)
        -> Sentence Object sortParam pat variable

deriving instance
    ( Eq (pat variable)
    , Eq sortParam
    ) => Eq (Sentence level sortParam pat variable)
deriving instance
    ( Show (pat variable)
    , Show sortParam
    ) => Show (Sentence level sortParam pat variable)

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module sentence sortParam pat variable = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![sentence sortParam pat variable]
    , moduleAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition sentence sortParam pat variable = Definition
    { definitionAttributes :: !(Attributes pat variable)
    , definitionModules    :: ![Module sentence sortParam pat variable]
    }
    deriving (Eq, Show)

class SentenceSymbolOrAlias sentence where
    getSentenceSymbolOrAliasConstructor
        :: sentence level pat variable -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level pat variable -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level pat variable -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level pat variable -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level pat variable -> Attributes pat variable
    getSentenceSymbolOrAliasSentenceName
        :: sentence level pat variable -> String
    getSentenceSymbolOrAliasHead
        :: sentence level pat variable -> [Sort level] -> SymbolOrAlias level
    getSentenceSymbolOrAliasHead sentence sortParameters = SymbolOrAlias
        { symbolOrAliasConstructor =
            getSentenceSymbolOrAliasConstructor sentence
        , symbolOrAliasParams = sortParameters
        }

instance SentenceSymbolOrAlias SentenceAlias where
    getSentenceSymbolOrAliasConstructor = aliasConstructor . sentenceAliasAlias
    getSentenceSymbolOrAliasSortParams = aliasParams . sentenceAliasAlias
    getSentenceSymbolOrAliasArgumentSorts = sentenceAliasSorts
    getSentenceSymbolOrAliasResultSort = sentenceAliasResultSort
    getSentenceSymbolOrAliasAttributes = sentenceAliasAttributes
    getSentenceSymbolOrAliasSentenceName _ = "alias"

instance SentenceSymbolOrAlias SentenceSymbol where
    getSentenceSymbolOrAliasConstructor =
        symbolConstructor . sentenceSymbolSymbol
    getSentenceSymbolOrAliasSortParams = symbolParams . sentenceSymbolSymbol
    getSentenceSymbolOrAliasArgumentSorts = sentenceSymbolSorts
    getSentenceSymbolOrAliasResultSort = sentenceSymbolResultSort
    getSentenceSymbolOrAliasAttributes = sentenceSymbolAttributes
    getSentenceSymbolOrAliasSentenceName _ = "symbol"

class AsSentence sentenceType s | s -> sentenceType where
    asSentence :: s -> sentenceType

data SortedPattern level variable metadata child = SortedPattern
    { sortedPatternPattern :: !(Pattern level variable metadata child)
    , sortedPatternSort    :: !(Sort level)
    }
    deriving (Eq, Show)

{-|'PatternStub' is either a pattern with a known sort, or a function that
builds a pattern from a sort.
-}
data PatternStub level variable metadata child
    = SortedPatternStub !(SortedPattern level variable metadata child)
    | UnsortedPatternStub (Sort level -> Pattern level variable metadata child)

{-|'withSort' transforms an 'UnsortedPatternStub' in a 'SortedPatternStub'.
-}
withSort
    :: Sort level
    -> PatternStub level variable metadata child
    -> PatternStub level variable metadata child
withSort s (UnsortedPatternStub p) =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = p s
        , sortedPatternSort = s
        }
withSort
    s
    p@(SortedPatternStub SortedPattern { sortedPatternSort = existingSort })
  =
    if s == existingSort
        then p
        else
            error
                (  "Unmatched sorts: "
                ++ show s
                ++ " and "
                ++ show existingSort
                ++ "."
                )
