{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Sentence
    ( Symbol (..)
    , groundSymbol
    , Alias (..)
    , SentenceAlias (..)
    , SentenceSymbol (..)
    , SentenceImport (..)
    , SentenceSort (..)
    , SentenceAxiom (..)
    , SentenceClaim (..)
    , SentenceHook (..)
    , Sentence (..)
    , sentenceAttributes
    , eraseSentenceAnnotations
    -- * Injections and projections
    , AsSentence (..)
    , SentenceSymbolOrAlias (..)
    -- * Type synonyms
    , PureSentenceSymbol
    , PureSentenceAlias
    , PureSentenceImport
    , PureSentenceAxiom
    , PureSentenceHook
    , PureSentence
    , PureModule
    , ParsedSentenceAlias
    , ParsedSentenceSymbol
    , ParsedSentenceImport
    , ParsedSentenceAxiom
    , ParsedSentenceSort
    , ParsedSentenceHook
    , ParsedSentence
    , ParsedModule
    -- * Re-exports
    , module Kore.Attribute.Attributes
    , module Kore.Syntax.Module
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
                 ( Hashable (..) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import           Kore.Attribute.Attributes
import qualified Kore.Attribute.Null as Attribute
                 ( Null (..) )
import           Kore.Sort
import           Kore.Syntax.Application
import           Kore.Syntax.Module
import           Kore.Syntax.Pattern
                 ( Pattern )
import           Kore.Syntax.Variable
import           Kore.Unparser

{- | @Symbol@ is the @head-constructor{sort-variable-list}@ part of the
@symbol-declaration@ syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).

See also: 'SymbolOrAlias'

 -}
data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Symbol

instance NFData Symbol

instance Unparse Symbol where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor
        <> parameters symbolParams

    unparse2 Symbol { symbolConstructor } =
        unparse2 symbolConstructor


-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id -> Symbol
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

{- | 'Alias' corresponds to the @head-constructor{sort-variable-list}@ part of
the @alias-declaration@ and @alias-declaration@ syntactic categories from the
Semantics of K, Section 9.1.6 (Declaration and Definitions).

See also: 'SymbolOrAlias'.

 -}
data Alias = Alias
    { aliasConstructor :: !Id
    , aliasParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Alias

instance NFData Alias

instance Unparse Alias where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor <> parameters aliasParams
    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

{- | 'SentenceAlias' corresponds to the @alias-declaration@ and syntactic
category from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

-}
data SentenceAlias (patternType :: *) =
    SentenceAlias
        { sentenceAliasAlias        :: !Alias
        , sentenceAliasSorts        :: ![Sort]
        , sentenceAliasResultSort   :: !Sort
        , sentenceAliasLeftPattern  :: !(Application SymbolOrAlias Variable)
        , sentenceAliasRightPattern :: !patternType
        , sentenceAliasAttributes   :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceAlias patternType)

instance NFData patternType => NFData (SentenceAlias patternType)

instance Unparse patternType => Unparse (SentenceAlias patternType) where
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
        Pretty.fillSep
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

    unparse2
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        Pretty.fillSep
            [ "alias"
            , unparse2 sentenceAliasAlias <> arguments2 sentenceAliasSorts
            , ":"
            , unparse2 sentenceAliasResultSort
            , "where"
            , unparse2 sentenceAliasLeftPattern
            , ":="
            , unparse2 sentenceAliasRightPattern
            , unparse2 sentenceAliasAttributes
            ]

{- | 'SentenceSymbol' is the @symbol-declaration@ and syntactic category from
the Semantics of K, Section 9.1.6 (Declaration and Definitions).

-}
data SentenceSymbol (patternType :: *) =
    SentenceSymbol
        { sentenceSymbolSymbol     :: !Symbol
        , sentenceSymbolSorts      :: ![Sort]
        , sentenceSymbolResultSort :: !Sort
        , sentenceSymbolAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSymbol patternType)

instance NFData (SentenceSymbol patternType)

instance Unparse (SentenceSymbol patternType) where
    unparse
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
      =
        Pretty.fillSep
            [ "symbol"
            , unparse sentenceSymbolSymbol <> arguments sentenceSymbolSorts
            , ":"
            , unparse sentenceSymbolResultSort
            , unparse sentenceSymbolAttributes
            ]

    unparse2
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
      = Pretty.vsep
            [ Pretty.fillSep [ "symbol", unparse2 sentenceSymbolSymbol ]
            , Pretty.fillSep [ "axiom \\forall s Sorts"
                             , Pretty.parens (Pretty.fillSep
                                   [ "\\subset"
                                   , Pretty.parens (Pretty.fillSep
                                       [ unparse2 sentenceSymbolSymbol
                                       , unparse2Inhabitant sentenceSymbolSorts
                                       ])
                                   , unparse2 sentenceSymbolResultSort
                                   ])
                             ]
            ]
          where unparse2Inhabitant ss =
                  case ss of
                      [] -> ""
                      (s : rest) ->
                        (Pretty.parens (Pretty.fillSep ["\\inh", unparse2 s]))
                        <> (unparse2Inhabitant rest)

{- | 'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
-- TODO (thomas.tuegel): Even though the parameters are unused, they must stay
-- to satisfy the functional dependencies on 'AsSentence' below. Because they
-- are phantom, every use of 'asSentence' for a 'SentenceImport' will require a
-- type ascription. We should refactor the class so this is not necessary and
-- remove the parameters.
data SentenceImport (patternType :: *) =
    SentenceImport
        { sentenceImportModuleName :: !ModuleName
        , sentenceImportAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceImport patternType)

instance NFData (SentenceImport patternType)

instance Unparse (SentenceImport patternType) where
    unparse
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse sentenceImportModuleName
            , unparse sentenceImportAttributes
            ]

    unparse2
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse2 sentenceImportModuleName
            , unparse2 sentenceImportAttributes
            ]

{- | 'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceSort (patternType :: *) =
    SentenceSort
        { sentenceSortName       :: !Id
        , sentenceSortParameters :: ![SortVariable]
        , sentenceSortAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSort patternType)

instance NFData (SentenceSort patternType)

instance Unparse (SentenceSort patternType) where
    unparse
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }
      =
        Pretty.fillSep
            [ "sort"
            , unparse sentenceSortName <> parameters sentenceSortParameters
            , unparse sentenceSortAttributes
            ]

    unparse2
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            }
      = Pretty.vsep
            [ Pretty.fillSep ["symbol", unparse2 sentenceSortName, "[sort]"]
            , Pretty.fillSep ["axiom"
                             , "\\subset"
                             , Pretty.parens (Pretty.fillSep
                                [ unparse2 sentenceSortName
                                , printLbSortsRb (length sentenceSortParameters)
                                ])
                             , "Sorts"
                             ]
            ]
      where printLbSortsRb n =
              case n of
                  0 -> ""
                  m -> Pretty.fillSep["(\\inh Sorts)", printLbSortsRb (m - 1)]

{- | 'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
data SentenceAxiom (patternType :: *) =
    SentenceAxiom
        { sentenceAxiomParameters :: ![SortVariable]
        , sentenceAxiomPattern    :: !patternType
        , sentenceAxiomAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceAxiom patternType)

instance NFData patternType => NFData (SentenceAxiom patternType)

instance Unparse patternType => Unparse (SentenceAxiom patternType) where
    unparse = unparseAxiom "axiom"
    unparse2 = unparseAxiom2 "axiom"

unparseAxiom
    :: Unparse patternType
    => Pretty.Doc ann
    -> SentenceAxiom patternType
    -> Pretty.Doc ann
unparseAxiom
    label
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , parameters sentenceAxiomParameters
        , unparse sentenceAxiomPattern
        , unparse sentenceAxiomAttributes
        ]

unparseAxiom2
    :: Unparse patternType
    => Pretty.Doc ann
    -> SentenceAxiom patternType
    -> Pretty.Doc ann
unparseAxiom2
    label
    SentenceAxiom
        { sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , unparse2 sentenceAxiomPattern
        , unparse2 sentenceAxiomAttributes
        ]

{- | 'SentenceClaim' corresponds to the @claim-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

 -}
newtype SentenceClaim (patternType :: *) =
    SentenceClaim { getSentenceClaim :: SentenceAxiom patternType }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceClaim patternType)

instance NFData patternType => NFData (SentenceClaim patternType)

instance Unparse patternType => Unparse (SentenceClaim patternType) where
    unparse = unparseAxiom "claim" . getSentenceClaim
    unparse2 = unparseAxiom2 "claim" . getSentenceClaim

{- | @SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

See also: 'SentenceSort', 'SentenceSymbol'

 -}
data SentenceHook (patternType :: *)
    = SentenceHookedSort !(SentenceSort patternType)
    | SentenceHookedSymbol !(SentenceSymbol patternType)
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceHook patternType)

instance NFData (SentenceHook patternType)

instance Unparse (SentenceHook patternType) where
    unparse =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse a
            SentenceHookedSymbol a -> "hooked-" <> unparse a

    unparse2 =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse2 a
            SentenceHookedSymbol a -> "hooked-" <> unparse2 a

{- | @Sentence@ is the @declaration@ syntactic category from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

-}
data Sentence (patternType :: *) where
    SentenceAliasSentence
        :: !(SentenceAlias patternType)
        -> Sentence patternType
    SentenceSymbolSentence
        :: !(SentenceSymbol patternType)
        -> Sentence patternType
    SentenceImportSentence
        :: !(SentenceImport patternType)
        -> Sentence patternType
    SentenceAxiomSentence
        :: !(SentenceAxiom patternType)
        -> Sentence patternType
    SentenceClaimSentence
        :: !(SentenceClaim patternType)
        -> Sentence patternType
    SentenceSortSentence
        :: !(SentenceSort patternType)
        -> Sentence patternType
    SentenceHookSentence
        :: !(SentenceHook patternType)
        -> Sentence patternType
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance NFData patternType => NFData (Sentence patternType)

instance Unparse patternType => Unparse (Sentence patternType) where
     unparse =
        \case
            SentenceAliasSentence s -> unparse s
            SentenceSymbolSentence s -> unparse s
            SentenceImportSentence s -> unparse s
            SentenceAxiomSentence s -> unparse s
            SentenceClaimSentence s -> unparse s
            SentenceSortSentence s -> unparse s
            SentenceHookSentence s -> unparse s

     unparse2 =
        \case
            SentenceAliasSentence s -> unparse2 s
            SentenceSymbolSentence s -> unparse2 s
            SentenceImportSentence s -> unparse2 s
            SentenceAxiomSentence s -> unparse2 s
            SentenceClaimSentence s -> unparse2 s
            SentenceSortSentence s -> unparse2 s
            SentenceHookSentence s -> unparse2 s

{- | The attributes associated with a sentence.

Every sentence type has attributes, so this operation is total.

 -}
sentenceAttributes :: Sentence patternType -> Attributes
sentenceAttributes =
    \case
        SentenceAliasSentence
            SentenceAlias { sentenceAliasAttributes } ->
                sentenceAliasAttributes
        SentenceSymbolSentence
            SentenceSymbol { sentenceSymbolAttributes } ->
                sentenceSymbolAttributes
        SentenceImportSentence
            SentenceImport { sentenceImportAttributes } ->
                sentenceImportAttributes
        SentenceAxiomSentence
            SentenceAxiom { sentenceAxiomAttributes } ->
                sentenceAxiomAttributes
        SentenceClaimSentence
            (SentenceClaim (SentenceAxiom { sentenceAxiomAttributes })) ->
                sentenceAxiomAttributes
        SentenceSortSentence
            SentenceSort { sentenceSortAttributes } ->
                sentenceSortAttributes
        SentenceHookSentence sentence ->
            case sentence of
                SentenceHookedSort
                    SentenceSort { sentenceSortAttributes } ->
                        sentenceSortAttributes
                SentenceHookedSymbol
                    SentenceSymbol { sentenceSymbolAttributes } ->
                        sentenceSymbolAttributes

-- | Erase the pattern annotations within a 'Sentence'.
eraseSentenceAnnotations
    :: Functor domain
    => Sentence (Pattern domain variable erased)
    -> Sentence (Pattern domain variable Attribute.Null)
eraseSentenceAnnotations sentence = (<$) Attribute.Null <$> sentence

class AsSentence sentenceType where
    asSentence :: sentenceType patternType -> Sentence patternType

instance AsSentence SentenceAlias where
    asSentence = SentenceAliasSentence

instance AsSentence SentenceSymbol where
    asSentence = SentenceSymbolSentence

instance AsSentence SentenceImport where
    asSentence = SentenceImportSentence

instance AsSentence SentenceAxiom where
    asSentence = SentenceAxiomSentence

instance AsSentence SentenceSort where
    asSentence = SentenceSortSentence

instance AsSentence SentenceHook where
    asSentence = SentenceHookSentence

class SentenceSymbolOrAlias (sentence :: * -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence patternType -> Id
    getSentenceSymbolOrAliasSortParams
        :: sentence patternType -> [SortVariable]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence patternType -> [Sort]
    getSentenceSymbolOrAliasResultSort
        :: sentence patternType -> Sort
    getSentenceSymbolOrAliasAttributes
        :: sentence patternType -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence patternType -> String
    getSentenceSymbolOrAliasHead
        :: sentence patternType
        -> [Sort]
        -> SymbolOrAlias
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

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom = SentenceAxiom ParsedPattern

-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias = SentenceAlias ParsedPattern

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol = SentenceSymbol ParsedPattern

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport = SentenceImport ParsedPattern

-- | 'PureSentenceHook' is the pure (fixed-@level@) version of 'SentenceHook'.
type PureSentenceHook = SentenceHook ParsedPattern

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence = Sentence ParsedPattern

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule = Module PureSentence

type ParsedSentenceSort = SentenceSort ParsedPattern

type ParsedSentenceSymbol = SentenceSymbol ParsedPattern

type ParsedSentenceAlias = SentenceAlias ParsedPattern

type ParsedSentenceImport = SentenceImport ParsedPattern

type ParsedSentenceAxiom = SentenceAxiom ParsedPattern

type ParsedSentenceHook = SentenceHook ParsedPattern

type ParsedSentence = Sentence ParsedPattern

type ParsedModule = Module ParsedSentence
