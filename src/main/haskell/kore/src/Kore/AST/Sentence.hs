{-|
Module      : Kore.AST.Common
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see Kore.AST.Kore for the unified
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
module Kore.AST.Sentence where

import Control.DeepSeq
       ( NFData (..) )
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Maybe
       ( catMaybes )
import GHC.Generics
       ( Generic )

import           Data.Functor.Foldable.Orphans ()
import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.Pretty
                 ( Pretty (..), (<+>), (<>) )
import qualified Kore.AST.Pretty as Pretty
import           Data.Proxy

{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}

newtype Attributes =
    Attributes { getAttributes :: [CommonKorePattern] }
  deriving (Eq, Generic, Show)

instance NFData Attributes

instance Pretty Attributes where
    pretty = Pretty.attributes . getAttributes

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceAlias level (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = SentenceAlias
    { sentenceAliasAlias        :: !(Alias level)
    , sentenceAliasSorts        :: ![Sort level]
    , sentenceAliasResultSort   :: !(Sort level)
    , sentenceAliasLeftPattern  :: !(Pattern level domain variable (Fix (pat domain variable)))
    , sentenceAliasRightPattern :: !(Pattern level domain variable (Fix (pat domain variable)))
    , sentenceAliasAttributes   :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance
    ( NFData (Fix (pat domain variable))
    , NFData (variable level)
    ) => NFData (SentenceAlias level pat domain variable)

instance (Pretty (variable level), Pretty (Fix (pat domain variable))) =>
    Pretty (SentenceAlias level pat domain variable) where
    pretty SentenceAlias {..} =
        Pretty.fillSep
        [ "alias"
        , pretty sentenceAliasAlias <> Pretty.arguments sentenceAliasSorts
        , ":"
        , pretty sentenceAliasResultSort
        , "where"
        , pretty sentenceAliasLeftPattern
        , ":="
        , pretty sentenceAliasRightPattern
        , pretty sentenceAliasAttributes
        ]

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol level (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol level)
    , sentenceSymbolSorts      :: ![Sort level]
    , sentenceSymbolResultSort :: !(Sort level)
    , sentenceSymbolAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceSymbol level pat domain variable)

instance Pretty (Fix (pat domain variable)) =>
    Pretty (SentenceSymbol level pat domain variable) where
    pretty SentenceSymbol {..} =
        Pretty.fillSep
        [ "symbol"
        , pretty sentenceSymbolSymbol <> Pretty.arguments sentenceSymbolSorts
        , ":"
        , pretty sentenceSymbolResultSort
        , pretty sentenceSymbolAttributes
        ]

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Eq, Generic, Ord, Show)

instance NFData ModuleName

instance Pretty ModuleName where
    pretty = Pretty.fromString . getModuleName

{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceImport (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceImport pat domain variable)

instance Pretty (Fix (pat domain variable)) =>
    Pretty (SentenceImport pat domain variable) where
    pretty SentenceImport {..} =
        Pretty.fillSep
        [ "import", pretty sentenceImportModuleName
        , pretty sentenceImportAttributes
        ]

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort level (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = SentenceSort
    { sentenceSortName       :: !(Id level)
    , sentenceSortParameters :: ![SortVariable level]
    , sentenceSortAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceSort level pat domain variable)

instance Pretty (Fix (pat domain variable)) =>
    Pretty (SentenceSort level pat domain variable) where
    pretty SentenceSort {..} =
        Pretty.fillSep
        [ "sort"
        , pretty sentenceSortName <> Pretty.parameters sentenceSortParameters
        , pretty sentenceSortAttributes
        ]

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom sortParam (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = SentenceAxiom
    { sentenceAxiomParameters :: ![sortParam]
    , sentenceAxiomPattern    :: !(Fix (pat domain variable))
    , sentenceAxiomAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance
    ( NFData sortParam
    , NFData (Fix (pat domain variable))
    ) =>
    NFData (SentenceAxiom sortParam pat domain variable)

instance
    ( Pretty param
    , Pretty (Fix (pat domain variable))
    ) => Pretty (SentenceAxiom param pat domain variable)
  where
    pretty SentenceAxiom {..} =
        Pretty.fillSep
        [ "axiom"
        , Pretty.parameters sentenceAxiomParameters
        , pretty sentenceAxiomPattern
        , pretty sentenceAxiomAttributes
        ]

{-|@SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
Note that we are reusing the 'SentenceSort' and 'SentenceSymbol' structures to
represent hooked sorts and hooked symbols.
-}
data SentenceHook level (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
    = SentenceHookedSort !(SentenceSort level pat domain variable)
    | SentenceHookedSymbol !(SentenceSymbol level pat domain variable)
  deriving (Eq, Generic, Show)

instance NFData (SentenceHook level pat domain variable)

instance
    Pretty (Fix (pat domain variable) )
    => Pretty (SentenceHook level pat domain variable)
  where
    pretty (SentenceHookedSort a)   = "hooked-" <> pretty a
    pretty (SentenceHookedSymbol a) = "hooked-" <> pretty a

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence level sortParam (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *) where
    SentenceAliasSentence
        :: !(SentenceAlias level pat domain variable)
        -> Sentence level sortParam pat domain variable
    SentenceSymbolSentence
        :: !(SentenceSymbol level pat domain variable)
        -> Sentence level sortParam pat domain variable
    SentenceImportSentence
        :: !(SentenceImport pat domain variable)
        -> Sentence Meta sortParam pat domain variable
    SentenceAxiomSentence
        :: !(SentenceAxiom sortParam pat domain variable)
        -> Sentence Meta sortParam pat domain variable
    SentenceSortSentence
        :: !(SentenceSort level pat domain variable)
        -> Sentence level sortParam pat domain variable
    SentenceHookSentence
        :: !(SentenceHook Object pat domain variable)
        -> Sentence Object sortParam pat domain variable

deriving instance
    ( Eq1 (pat domain variable), Eq (pat domain variable (Fix (pat domain variable)))
    , Eq sortParam
    , Eq (variable level)
    ) => Eq (Sentence level sortParam pat domain variable)

instance
    ( NFData sortParam
    , NFData (variable level)
    , NFData (Fix (pat domain variable))
    ) =>
    NFData (Sentence level sortParam pat domain variable)
  where
    rnf =
        \case
            SentenceAliasSentence p -> rnf p
            SentenceSymbolSentence p -> rnf p
            SentenceImportSentence p -> rnf p
            SentenceAxiomSentence p -> rnf p
            SentenceSortSentence p -> rnf p
            SentenceHookSentence p -> rnf p

deriving instance
    ( Show1 (pat domain variable), Show (pat domain variable (Fix (pat domain variable)))
    , Show sortParam
    , Show (variable level)
    ) => Show (Sentence level sortParam pat domain variable)

instance
    ( Pretty sortParam
    , Pretty (Fix (pat domain variable))
    , Pretty (variable level)
    ) => Pretty (Sentence level sortParam pat domain variable)
  where
    pretty (SentenceAliasSentence s)  = pretty s
    pretty (SentenceSymbolSentence s) = pretty s
    pretty (SentenceImportSentence s) = pretty s
    pretty (SentenceAxiomSentence s)  = pretty s
    pretty (SentenceSortSentence s)   = pretty s
    pretty (SentenceHookSentence s)   = pretty s

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module sentence sortParam (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![sentence sortParam pat domain variable]
    , moduleAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance
    NFData (sentence sortParam pat domain variable) =>
    NFData (Module sentence sortParam pat domain variable)

instance
    ( Pretty (sentence sort pat domain variable)
    , Pretty (Fix (pat domain variable))
    ) => Pretty (Module sentence sort pat domain variable)
  where
    pretty Module {..} =
        (Pretty.vsep . catMaybes)
        [ Just ("module" <+> pretty moduleName)
        , case moduleSentences of
            [] -> Nothing
            _ -> Just ((Pretty.indent 4 . Pretty.vsep) (pretty <$> moduleSentences))
        , Just "endmodule"
        , Just (pretty moduleAttributes)
        ]

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition sentence sortParam (pat :: * -> (* -> *) -> * -> *) domain (variable :: * -> *)
 = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: ![Module sentence sortParam pat domain variable]
    }
  deriving (Eq, Generic, Show)

instance
    NFData (sentence sortParam pat domain variable) =>
    NFData (Definition sentence sortParam pat domain variable)

instance
    ( Pretty (sentence sort pat domain variable)
    , Pretty (Fix (pat domain variable))
    ) => Pretty (Definition sentence sort pat domain variable)
  where
    pretty Definition {..} =
        Pretty.vsep (pretty definitionAttributes : map pretty definitionModules)

class SentenceSymbolOrAlias (sentence :: * -> (* -> (* -> *) -> * -> *) -> * -> (* -> *) -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence level pat domain variable -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level pat domain variable -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level pat domain variable -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level pat domain variable -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level pat domain variable -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence level pat domain variable -> String
    getSentenceSymbolOrAliasHead
        :: sentence level pat domain variable -> [Sort level] -> SymbolOrAlias level
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

-- |'KoreSentenceAlias' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAlias'
type KoreSentenceAlias level = SentenceAlias level UnifiedPattern KoreDomain Variable
-- |'KoreSentenceSymbol' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSymbol'
type KoreSentenceSymbol level = SentenceSymbol level UnifiedPattern KoreDomain Variable
-- |'KoreSentenceImport' is the Kore ('Meta' and 'Object') version of
-- 'SentenceImport'
type KoreSentenceImport = SentenceImport UnifiedPattern KoreDomain Variable
-- |'KoreSentenceAxiom' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAxiom'
type KoreSentenceAxiom = SentenceAxiom UnifiedSortVariable UnifiedPattern KoreDomain Variable
-- |'KoreSentenceSort' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSort'
type KoreSentenceSort level = SentenceSort level UnifiedPattern KoreDomain Variable
-- |'KoreSentenceHook' Kore ('Meta' and 'Object') version of
-- 'SentenceHook'
type KoreSentenceHook = SentenceHook Object UnifiedPattern KoreDomain Variable

{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Sentence',
to allow using toghether both 'Meta' and 'Object' sentences.
-}
-- newtype UnifiedSentence sortParam pat domain variable = UnifiedSentence
--     { getUnifiedSentence :: Unified (Rotate41 Sentence sortParam pat domain variable) }
--   deriving (Generic)

data UnifiedSentence sortParam pat domain variable 
  = UnifiedObjectSentence (Sentence Object sortParam pat domain variable)
  | UnifiedMetaSentence   (Sentence Meta   sortParam pat domain variable)
      deriving (Generic)

getMetaOrObjectSentenceType
    :: forall level sortParam pat domain variable .
       MetaOrObject level
    => Sentence level sortParam pat domain variable -> IsMetaOrObject level
getMetaOrObjectSentenceType _ = isMetaOrObject (Proxy :: Proxy level)

asUnifiedSentence
    :: MetaOrObject level
    => Sentence level sortParam pat domain variable
    -> UnifiedSentence sortParam pat domain variable
asUnifiedSentence sentence = case getMetaOrObjectSentenceType sentence of
    IsMeta   -> UnifiedMetaSentence   sentence
    IsObject -> UnifiedObjectSentence sentence

deriving instance
    ( Eq1 (pat domain variable), Eq (pat domain variable (Fix (pat domain variable)))
    , Eq sortParam
    , EqMetaOrObject variable
    ) => Eq (UnifiedSentence sortParam pat domain variable)

instance
    ( NFData sortParam
    , NFData (variable Meta), NFData (variable Object)
    , NFData (Fix (pat domain variable))
    ) =>
    NFData (UnifiedSentence sortParam pat domain variable)

deriving instance
    ( Show1 (pat domain variable), Show (pat domain variable (Fix (pat domain variable)))
    , Show sortParam
    , ShowMetaOrObject variable
    ) => Show (UnifiedSentence sortParam pat domain variable)

instance
    ( Pretty sortParam
    , Pretty (Fix (pat domain variable))
    , Pretty (variable Meta)
    , Pretty (variable Object)
    ) => Pretty (UnifiedSentence sortParam pat domain variable)
  where
    pretty = applyUnifiedSentence pretty pretty


-- |'KoreSentence' instantiates 'UnifiedSentence' to describe sentences fully
-- corresponding to the @declaration@ syntactic category
-- from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreSentence = UnifiedSentence UnifiedSortVariable UnifiedPattern KoreDomain Variable

constructUnifiedSentence
    :: (MetaOrObject level)
    => (a -> Sentence level sortParam pat domain variable)
    -> (a -> UnifiedSentence sortParam pat domain variable)
constructUnifiedSentence ctor = asUnifiedSentence . ctor

-- |Given functions appliable to 'Meta' 'Sentence's and 'Object' 'Sentences's,
-- builds a combined function which can be applied on 'UnifiedSentence's.
applyUnifiedSentence
    :: (Sentence Meta sortParam pat domain variable -> b)
    -> (Sentence Object sortParam pat domain variable -> b)
    -> (UnifiedSentence sortParam pat domain variable -> b)
applyUnifiedSentence metaT _ (UnifiedMetaSentence rs) =
    metaT rs
applyUnifiedSentence _ objectT (UnifiedObjectSentence rs) =
    objectT rs


-- |'KoreModule' fully instantiates 'Module' to correspond to the second, third,
-- and forth non-terminals of the @definition@ syntactic category from the
-- Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreModule =
    Module UnifiedSentence UnifiedSortVariable UnifiedPattern KoreDomain Variable

type KoreDefinition =
    Definition UnifiedSentence UnifiedSortVariable UnifiedPattern KoreDomain Variable

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceAlias level)
  where
    asSentence = asUnifiedSentence . SentenceAliasSentence

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceSymbol level)
  where
    asSentence = asUnifiedSentence . SentenceSymbolSentence

instance AsSentence KoreSentence KoreSentenceImport where
    asSentence = asUnifiedSentence . SentenceImportSentence

instance AsSentence KoreSentence KoreSentenceAxiom where
    asSentence = asUnifiedSentence . SentenceAxiomSentence

instance
  ( MetaOrObject level
  ) => AsSentence KoreSentence (KoreSentenceSort level) where
    asSentence = asUnifiedSentence . SentenceSortSentence

instance AsSentence KoreSentence KoreSentenceHook where
    asSentence = asUnifiedSentence . SentenceHookSentence
