{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
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
module Data.Kore.AST.Sentence where

import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.HaskellExtensions (Rotate41 (..))


{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}

newtype Attributes =
    Attributes { getAttributes :: [CommonKorePattern] }

deriving instance
    (Eq CommonKorePattern)
     => Eq Attributes

deriving instance
    (Show CommonKorePattern)
     => Show Attributes

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceAlias level (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = SentenceAlias
    { sentenceAliasAlias        :: !(Alias level)
    , sentenceAliasSorts        :: ![Sort level]
    , sentenceAliasResultSort   :: !(Sort level)
    , sentenceAliasLeftPattern  :: !(Pattern level variable (Fix (pat variable)))
    , sentenceAliasRightPattern :: !(Pattern level variable (Fix (pat variable)))
    , sentenceAliasAttributes   :: !Attributes
    }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq (variable level)
    )
    => Eq (SentenceAlias level pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show (variable level)
    )
    => Show (SentenceAlias level pat variable)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol level (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol level)
    , sentenceSymbolSorts      :: ![Sort level]
    , sentenceSymbolResultSort :: !(Sort level)
    , sentenceSymbolAttributes :: !Attributes
    }

deriving instance
    (Eq (pat variable (Fix (pat variable))))
     => Eq (SentenceSymbol level pat variable)

deriving instance
    (Show (pat variable (Fix (pat variable))))
     => Show (SentenceSymbol level pat variable)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq, Ord)

{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceImport (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !Attributes
    }

deriving instance
    (Eq (pat variable (Fix (pat variable))))
     => Eq (SentenceImport pat variable)

deriving instance
    (Show (pat variable (Fix (pat variable))))
     => Show (SentenceImport pat variable)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort level (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = SentenceSort
    { sentenceSortName       :: !(Id level)
    , sentenceSortParameters :: ![SortVariable level]
    , sentenceSortAttributes :: !Attributes
    }

deriving instance
    (Eq (pat variable (Fix (pat variable))))
     => Eq (SentenceSort level pat variable)

deriving instance
    (Show (pat variable (Fix (pat variable))))
     => Show (SentenceSort level pat variable)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom sortParam (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = SentenceAxiom
    { sentenceAxiomParameters :: ![sortParam]
    , sentenceAxiomPattern    :: !(Fix (pat variable))
    , sentenceAxiomAttributes :: !Attributes
    }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq sortParam
    )  => Eq (SentenceAxiom sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show sortParam
    ) => Show (SentenceAxiom sortParam pat variable)

{-|@SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
Note that we are reusing the 'SentenceSort' and 'SentenceSymbol' structures to
represent hooked sorts and hooked symbols.
-}
data SentenceHook level (pat :: (* -> *) -> * -> *) (variable :: * -> *)
    = SentenceHookedSort !(SentenceSort level pat variable)
    | SentenceHookedSymbol !(SentenceSymbol level pat variable)

deriving instance
    (Eq (pat variable (Fix (pat variable))))
     => Eq (SentenceHook level pat variable)

deriving instance
    (Show (pat variable (Fix (pat variable))))
     => Show (SentenceHook level pat variable)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence level sortParam (pat :: (* -> *) -> * -> *) (variable :: * -> *) where
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
    SentenceHookSentence
        :: !(SentenceHook Object pat variable)
        -> Sentence Object sortParam pat variable

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq sortParam
    , Eq (variable level)
    ) => Eq (Sentence level sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show sortParam
    , Show (variable level)
    ) => Show (Sentence level sortParam pat variable)

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module sentence sortParam (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![sentence sortParam pat variable]
    , moduleAttributes :: !Attributes
    }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq (sentence sortParam pat variable)
    ) => Eq (Module sentence sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show (sentence sortParam pat variable)
    ) => Show (Module sentence sortParam pat variable)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition sentence sortParam (pat :: (* -> *) -> * -> *) (variable :: * -> *)
 = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: ![Module sentence sortParam pat variable]
    }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq (sentence sortParam pat variable)
    ) => Eq (Definition sentence sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show (sentence sortParam pat variable)
    ) => Show (Definition sentence sortParam pat variable)

class SentenceSymbolOrAlias (sentence :: * -> ((* -> *) -> * -> *) -> (* -> *) -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence level pat variable -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level pat variable -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level pat variable -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level pat variable -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level pat variable -> Attributes
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

-- |'KoreSentenceAlias' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAlias'
type KoreSentenceAlias level = SentenceAlias level UnifiedPattern Variable
-- |'KoreSentenceSymbol' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSymbol'
type KoreSentenceSymbol level = SentenceSymbol level UnifiedPattern Variable
-- |'KoreSentenceImport' is the Kore ('Meta' and 'Object') version of
-- 'SentenceImport'
type KoreSentenceImport = SentenceImport UnifiedPattern Variable
-- |'KoreSentenceAxiom' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAxiom'
type KoreSentenceAxiom = SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
-- |'KoreSentenceSort' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSort'
type KoreSentenceSort = SentenceSort Object UnifiedPattern Variable
-- |'KoreSentenceHook' Kore ('Meta' and 'Object') version of
-- 'SentenceHook'
type KoreSentenceHook = SentenceHook Object UnifiedPattern Variable

{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Sentence',
to allow using toghether both 'Meta' and 'Object' sentences.
-}
newtype UnifiedSentence sortParam pat variable = UnifiedSentence
    { getUnifiedSentence :: Unified (Rotate41 Sentence sortParam pat variable) }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq sortParam
    , Eq (variable Meta)
    , Eq (variable Object)
    ) => Eq (UnifiedSentence sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show sortParam
    , Show (variable Meta)
    , Show (variable Object)
    ) => Show (UnifiedSentence sortParam pat variable)


-- |'KoreSentence' instantiates 'UnifiedSentence' to describe sentences fully
-- corresponding to the @declaration@ syntactic category
-- from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreSentence = UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

constructUnifiedSentence
    :: (MetaOrObject level)
    => (a -> Sentence level sortParam pat variable)
    -> (a -> UnifiedSentence sortParam pat variable)
constructUnifiedSentence ctor = UnifiedSentence . asUnified . Rotate41 . ctor

-- |Given functions appliable to 'Meta' 'Sentence's and 'Object' 'Sentences's,
-- builds a combined function which can be applied on 'UnifiedSentence's.
applyUnifiedSentence
    :: (Sentence Meta sortParam pat variable -> b)
    -> (Sentence Object sortParam pat variable -> b)
    -> (UnifiedSentence sortParam pat variable -> b)
applyUnifiedSentence metaT _ (UnifiedSentence (UnifiedMeta rs)) =
    metaT (unRotate41 rs)
applyUnifiedSentence _ objectT (UnifiedSentence (UnifiedObject rs)) =
    objectT (unRotate41 rs)


-- |'KoreModule' fully instantiates 'Module' to correspond to the second, third,
-- and forth non-terminals of the @definition@ syntactic category from the
-- Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreModule =
    Module UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

type KoreDefinition =
    Definition UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceAlias level)
  where
    asSentence = constructUnifiedSentence SentenceAliasSentence

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceSymbol level)
  where
    asSentence = constructUnifiedSentence SentenceSymbolSentence

instance AsSentence KoreSentence KoreSentenceImport where
    asSentence = constructUnifiedSentence SentenceImportSentence

instance AsSentence KoreSentence KoreSentenceAxiom where
    asSentence = constructUnifiedSentence SentenceAxiomSentence

instance AsSentence KoreSentence KoreSentenceSort where
    asSentence = constructUnifiedSentence SentenceSortSentence

instance AsSentence KoreSentence KoreSentenceHook where
    asSentence = constructUnifiedSentence SentenceHookSentence
